use std::net::{IpAddr, SocketAddr, ToSocketAddrs as _};
#[cfg(feature = "dns-resolver")]
use std::{future::Future, io, pin::Pin, sync::Arc, time::Duration};

use anyhow::Context;
use async_trait::async_trait;
use easytier_core::host::dns::{DnsQuery, DnsRecordResolver, DnsResolver, DnsSrvRecord};
use easytier_core::socket::SocketContext;
#[cfg(feature = "dns-resolver")]
use hickory_proto::runtime::{RuntimeProvider, TokioRuntimeProvider, iocompat::AsyncIoTokioAsStd};
#[cfg(feature = "dns-resolver")]
use hickory_proto::xfer::Protocol;
#[cfg(feature = "dns-resolver")]
use hickory_resolver::config::{LookupIpStrategy, NameServerConfig, ResolverConfig, ResolverOpts};
#[cfg(feature = "dns-resolver")]
use hickory_resolver::name_server::{GenericConnector, TokioConnectionProvider};
#[cfg(feature = "dns-resolver")]
use hickory_resolver::system_conf::read_system_conf;
#[cfg(feature = "dns-resolver")]
use hickory_resolver::{Resolver, TokioResolver};
#[cfg(feature = "dns-resolver")]
use once_cell::sync::Lazy;
use tokio::net::lookup_host;
#[cfg(feature = "dns-resolver")]
use tokio::net::{TcpStream, UdpSocket};
#[cfg(feature = "dns-resolver")]
use tokio::sync::Semaphore;

use super::error::Error;
use super::netns::NetNS;
#[cfg(feature = "dns-resolver")]
use crate::{
    socket::{tcp::create_tcp_socket, udp::create_udp_socket},
    socket_protector::native_socket_protection_available,
};
#[cfg(feature = "dns-resolver")]
use easytier_core::socket::{NetNamespace, tcp::TcpBindOptions, udp::UdpBindOptions};

#[cfg(feature = "dns-resolver")]
pub fn get_default_resolver_config() -> ResolverConfig {
    let mut default_resolve_config = ResolverConfig::new();
    default_resolve_config.add_name_server(NameServerConfig::new(
        "223.5.5.5:53".parse().unwrap(),
        Protocol::Udp,
    ));
    default_resolve_config.add_name_server(NameServerConfig::new(
        "180.184.1.1:53".parse().unwrap(),
        Protocol::Udp,
    ));
    default_resolve_config
}

#[cfg(feature = "dns-resolver")]
fn append_legacy_name_servers(config: &mut ResolverConfig, system: Option<&ResolverConfig>) {
    for name_server in get_default_resolver_config().name_servers() {
        config.add_name_server(name_server.clone());
    }
    if let Some(system) = system {
        for name_server in system.name_servers() {
            config.add_name_server(name_server.clone());
        }
    }
}

/// User-facing DNS-over-HTTPS settings.
#[cfg(feature = "doh")]
#[derive(Debug, Clone)]
pub struct DohSettings {
    /// DoH endpoint, e.g. `https://dns.google/dns-query` or `https://1.1.1.1/dns-query`.
    pub url: String,
    /// Pinned IP used to reach the DoH server. Required when the url host is a
    /// domain and `only` is set; otherwise a single plaintext bootstrap lookup
    /// resolves it.
    pub bootstrap_ip: Option<IpAddr>,
    /// Overrides the TLS server name used for SNI and certificate validation.
    pub tls_name: Option<String>,
    /// Forbids falling back to plaintext DNS.
    pub only: bool,
    /// PEM file with a CA chain to trust instead of the webpki roots, for
    /// privately hosted DoH servers.
    pub ca_cert_path: Option<String>,
}

/// A validated, bootstrap-resolved DoH name server.
#[cfg(feature = "dns-resolver")]
#[derive(Debug)]
pub(crate) struct DohServerConfig {
    pub(crate) name_server: NameServerConfig,
    /// DER-encoded CA certificates to trust instead of the webpki roots.
    pub(crate) ca_certs_der: Vec<Vec<u8>>,
    pub(crate) only: bool,
}

#[cfg(feature = "doh")]
static DOH_CONFIG: std::sync::Mutex<Option<Arc<DohServerConfig>>> = std::sync::Mutex::new(None);

/// Installs the process-global DoH configuration. Must run before the first
/// DNS lookup: the static resolver snapshots the configuration lazily and
/// contextual resolvers snapshot it per request.
#[cfg(feature = "doh")]
pub async fn init_doh(settings: DohSettings) -> anyhow::Result<()> {
    let config = resolve_doh_config(&settings).await?;
    *DOH_CONFIG.lock().unwrap() = Some(Arc::new(config));
    tracing::info!(
        url = %settings.url,
        only = settings.only,
        "DoH resolver configured"
    );
    Ok(())
}

/// Resolves the DoH server domain with the system resolver when no bootstrap
/// ip was given. This is a single plaintext lookup that only reveals the DoH
/// server's own domain.
/// The host part of a DoH endpoint url, normalized (IPv6 without brackets).
#[cfg(feature = "doh")]
#[derive(Debug, Clone, PartialEq, Eq)]
enum DohUrlHost {
    Ip(IpAddr),
    Domain(String),
}

/// Parses and validates the DoH endpoint url into its host, port and
/// http endpoint path. Uses `url::Host` so IPv6 literals work with or
/// without the brackets `host_str()` would render.
#[cfg(feature = "doh")]
fn parse_doh_url(url: &str) -> anyhow::Result<(DohUrlHost, u16, String)> {
    let parsed = url::Url::parse(url).with_context(|| format!("invalid DoH url: {url}"))?;
    anyhow::ensure!(
        parsed.scheme() == "https",
        "DoH url must use the https scheme: {url}"
    );
    anyhow::ensure!(
        parsed.query().is_none(),
        "DoH url must not contain a query string: {url}"
    );
    let host = match parsed.host() {
        Some(url::Host::Ipv4(ip)) => DohUrlHost::Ip(IpAddr::V4(ip)),
        Some(url::Host::Ipv6(ip)) => DohUrlHost::Ip(IpAddr::V6(ip)),
        Some(url::Host::Domain(domain)) => DohUrlHost::Domain(domain.to_string()),
        None => anyhow::bail!("DoH url has no host: {url}"),
    };
    let port = parsed.port_or_known_default().unwrap_or(443);
    let path = parsed.path();
    let endpoint = if path.is_empty() || path == "/" {
        "/dns-query".to_string()
    } else {
        path.to_string()
    };
    Ok((host, port, endpoint))
}

#[cfg(feature = "doh")]
pub(crate) async fn resolve_doh_config(settings: &DohSettings) -> anyhow::Result<DohServerConfig> {
    let (host, port, _) = parse_doh_url(&settings.url)?;

    let mut bootstrap = settings.bootstrap_ip;
    if let DohUrlHost::Domain(domain) = &host {
        if bootstrap.is_none() {
            if settings.only {
                anyhow::bail!(
                    "doh_only requires a bootstrap ip when the DoH url host is a domain ({domain})"
                );
            }
            bootstrap = Some(resolve_doh_bootstrap(domain, port).await?);
        }
    }

    let name_server = build_doh_name_server(&settings.url, bootstrap, settings.tls_name.as_deref())?;
    let ca_certs_der = match &settings.ca_cert_path {
        Some(path) => parse_pem_certs(path)?
            .into_iter()
            .map(|cert| cert.to_vec())
            .collect(),
        None => Vec::new(),
    };
    Ok(DohServerConfig {
        name_server,
        ca_certs_der,
        only: settings.only,
    })
}

#[cfg(feature = "doh")]
async fn resolve_doh_bootstrap(host: &str, port: u16) -> anyhow::Result<IpAddr> {
    tokio::net::lookup_host((host, port))
        .await
        .with_context(|| format!("failed to bootstrap resolve DoH server domain: {host}"))?
        .next()
        .with_context(|| format!("DoH server domain resolved to no addresses: {host}"))
        .map(|addr| addr.ip())
}

/// Maps a DoH endpoint url onto hickory's name server config. The pinned
/// `bootstrap_ip` (or the literal IP in the url) becomes the socket address,
/// while the domain (or the explicit override) stays the TLS server name, so
/// certificate validation is independent of how the server is reached.
#[cfg(feature = "doh")]
pub(crate) fn build_doh_name_server(
    url: &str,
    bootstrap_ip: Option<IpAddr>,
    tls_name_override: Option<&str>,
) -> anyhow::Result<NameServerConfig> {
    let (host, port, endpoint) = parse_doh_url(url)?;

    let ip = match &host {
        DohUrlHost::Ip(ip) => *ip,
        DohUrlHost::Domain(domain) => bootstrap_ip.with_context(|| {
            format!("DoH url host is a domain ({domain}), a bootstrap ip is required")
        })?,
    };
    // The tls name stays a plain address literal for IPv6 (no brackets) so
    // rustls parses it as a ServerName::IpAddress.
    let tls_name = tls_name_override
        .map(ToString::to_string)
        .unwrap_or(match &host {
            DohUrlHost::Ip(ip) => ip.to_string(),
            DohUrlHost::Domain(domain) => domain.clone(),
        });

    let mut name_server = NameServerConfig::new(SocketAddr::new(ip, port), Protocol::Https);
    name_server.tls_dns_name = Some(tls_name);
    name_server.http_endpoint = Some(endpoint);
    Ok(name_server)
}

#[cfg(feature = "doh")]
fn parse_pem_certs(path: &str) -> anyhow::Result<Vec<rustls::pki_types::CertificateDer<'static>>> {
    use base64::Engine as _;

    let content = std::fs::read_to_string(path)
        .with_context(|| format!("failed to read DoH CA cert file: {path}"))?;
    let mut certs = Vec::new();
    let mut current: Option<String> = None;
    for line in content.lines() {
        let line = line.trim();
        if line == "-----BEGIN CERTIFICATE-----" {
            current = Some(String::new());
        } else if line == "-----END CERTIFICATE-----" {
            let body = current.take().with_context(|| {
                format!("malformed PEM in {path}: end marker without start marker")
            })?;
            let der = base64::engine::general_purpose::STANDARD
                .decode(body)
                .with_context(|| format!("malformed base64 in PEM file {path}"))?;
            certs.push(rustls::pki_types::CertificateDer::from(der));
        } else if let Some(body) = current.as_mut() {
            if !line.is_empty() {
                body.push_str(line);
            }
        }
    }
    anyhow::ensure!(!certs.is_empty(), "no PEM certificates found in {path}");
    Ok(certs)
}

#[cfg(feature = "doh")]
impl DohServerConfig {
    fn tls_client_config(&self) -> rustls::ClientConfig {
        let provider = Arc::new(rustls::crypto::ring::default_provider());
        let builder = rustls::ClientConfig::builder_with_provider(provider)
            .with_safe_default_protocol_versions()
            .expect("rustls supports the default protocol versions");
        let mut roots = rustls::RootCertStore::empty();
        if self.ca_certs_der.is_empty() {
            roots.extend(webpki_roots::TLS_SERVER_ROOTS.iter().cloned());
        } else {
            for cert in &self.ca_certs_der {
                roots
                    .add(rustls::pki_types::CertificateDer::from(cert.clone()))
                    .expect("CA certificates are validated when the DoH config is built");
            }
        }
        builder.with_root_certificates(roots).with_no_client_auth()
    }
}

#[cfg(feature = "dns-resolver")]
pub(crate) fn current_doh() -> Option<Arc<DohServerConfig>> {
    #[cfg(feature = "doh")]
    {
        DOH_CONFIG.lock().unwrap().clone()
    }
    #[cfg(not(feature = "doh"))]
    {
        None
    }
}

/// How long a DoH lookup may take before falling back (or failing, in
/// `only` mode). Cold lookups pay one TCP + TLS + HTTP/2 handshake.
#[cfg(all(feature = "dns-resolver", feature = "doh"))]
const DOH_LOOKUP_TIMEOUT: Duration = Duration::from_secs(5);

/// Tries the DoH resolver first and falls back to the provided future only
/// when plaintext DNS is allowed.
#[cfg(feature = "dns-resolver")]
async fn lookup_via_doh_first<FDoH, FFallback>(
    doh: Option<&DohServerConfig>,
    doh_lookup: FDoH,
    fallback: FFallback,
) -> anyhow::Result<Vec<IpAddr>>
where
    FDoH: Future<Output = anyhow::Result<Vec<IpAddr>>>,
    FFallback: Future<Output = anyhow::Result<Vec<IpAddr>>>,
{
    #[cfg(feature = "doh")]
    {
        if let Some(doh) = doh {
            return lookup_via_doh_first_with_timeout(doh, DOH_LOOKUP_TIMEOUT, doh_lookup, fallback)
                .await;
        }
    }
    #[cfg(not(feature = "doh"))]
    {
        let _ = doh;
    }
    doh_lookup.await
}

#[cfg(all(feature = "dns-resolver", feature = "doh"))]
async fn lookup_via_doh_first_with_timeout<FDoH, FFallback>(
    doh: &DohServerConfig,
    timeout: Duration,
    doh_lookup: FDoH,
    fallback: FFallback,
) -> anyhow::Result<Vec<IpAddr>>
where
    FDoH: Future<Output = anyhow::Result<Vec<IpAddr>>>,
    FFallback: Future<Output = anyhow::Result<Vec<IpAddr>>>,
{
    match tokio::time::timeout(timeout, doh_lookup).await {
        Ok(Ok(addrs)) => {
            tracing::debug!(?addrs, "doh lookup done");
            return Ok(addrs);
        }
        Ok(Err(error)) => {
            tracing::warn!(?error, "doh lookup failed");
        }
        Err(_) => {
            tracing::warn!(?timeout, "doh lookup timed out");
        }
    }
    if doh.only {
        anyhow::bail!("DoH lookup failed and plaintext DNS is disabled (doh_only)");
    }
    fallback.await
}

#[cfg(feature = "dns-resolver")]
fn resolver_config_with(doh: Option<&DohServerConfig>) -> (ResolverConfig, ResolverOpts) {
    let mut options = ResolverOpts::default();
    let mut system_config: Option<ResolverConfig> = None;
    if let Ok((system_conf, system_opts)) = read_system_conf() {
        system_config = Some(system_conf);
        options = system_opts;
    }

    let mut config = ResolverConfig::new();
    if let Some(doh) = doh {
        config.add_name_server(doh.name_server.clone());
        #[cfg(feature = "doh")]
        {
            options.tls_config = doh.tls_client_config();
        }
    }
    let doh_only = doh.map(|doh| doh.only).unwrap_or(false);
    if !doh_only {
        append_legacy_name_servers(&mut config, system_config.as_ref());
    }
    options.ip_strategy = LookupIpStrategy::Ipv4AndIpv6;
    (config, options)
}

#[cfg(feature = "dns-resolver")]
fn resolver_config() -> (ResolverConfig, ResolverOpts) {
    #[cfg(feature = "doh")]
    {
        resolver_config_with(current_doh().as_deref())
    }
    #[cfg(not(feature = "doh"))]
    {
        resolver_config_with(None)
    }
}

#[cfg(feature = "dns-resolver")]
fn build_resolver(doh: Option<&DohServerConfig>) -> Resolver<GenericConnector<TokioRuntimeProvider>>
{
    let (config, options) = resolver_config_with(doh);
    TokioResolver::builder_with_config(config, TokioConnectionProvider::default())
        .with_options(options)
        .build()
}

#[cfg(feature = "dns-resolver")]
static RESOLVER: Lazy<Arc<Resolver<GenericConnector<TokioRuntimeProvider>>>> = Lazy::new(|| {
    #[cfg(feature = "doh")]
    {
        Arc::new(build_resolver(current_doh().as_deref()))
    }
    #[cfg(not(feature = "doh"))]
    {
        Arc::new(build_resolver(None))
    }
});

#[cfg(feature = "dns-resolver")]
const SYSTEM_DNS_LOOKUP_TIMEOUT: Duration = Duration::from_millis(800);

#[cfg(feature = "dns-resolver")]
#[derive(Debug)]
struct SystemDnsResolver {
    lookup_slot: Arc<Semaphore>,
    timeout: Duration,
}

#[cfg(feature = "dns-resolver")]
impl Default for SystemDnsResolver {
    fn default() -> Self {
        Self::new(SYSTEM_DNS_LOOKUP_TIMEOUT)
    }
}

#[cfg(feature = "dns-resolver")]
impl SystemDnsResolver {
    fn new(timeout: Duration) -> Self {
        Self {
            lookup_slot: Arc::new(Semaphore::new(1)),
            timeout,
        }
    }

    async fn resolve<SystemFuture, FallbackFuture>(
        &self,
        system_lookup: SystemFuture,
        fallback_lookup: FallbackFuture,
    ) -> anyhow::Result<Vec<IpAddr>>
    where
        SystemFuture: Future<Output = anyhow::Result<Vec<IpAddr>>> + Send + 'static,
        FallbackFuture: Future<Output = anyhow::Result<Vec<IpAddr>>> + Send,
    {
        // Tokio runs getaddrinfo on its blocking pool and cannot cancel it.
        // Keep the permit in a detached task after a timeout so reconnects do
        // not accumulate blocked system lookups. Once it finishes, later
        // requests can use the system resolver again.
        let lookup_slot = self.lookup_slot.clone();
        let system_attempt = async move {
            let permit = lookup_slot
                .acquire_owned()
                .await
                .context("system DNS lookup slot closed")?;
            tokio::spawn(async move {
                let _permit = permit;
                system_lookup.await
            })
            .await
            .context("system DNS lookup task failed")?
        };

        match tokio::time::timeout(self.timeout, system_attempt).await {
            Ok(Ok(addresses)) => {
                tracing::debug!(?addresses, "system dns lookup done");
                return Ok(addresses);
            }
            Ok(Err(error)) => {
                tracing::warn!(?error, "system dns lookup failed, fallback to hickory");
            }
            Err(_) => {
                tracing::warn!(
                    timeout = ?self.timeout,
                    "system dns lookup timed out, fallback to hickory"
                );
            }
        }

        fallback_lookup.await
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct RuntimeDnsIoContext {
    netns: Option<String>,
    socket_mark: Option<u32>,
}

impl RuntimeDnsIoContext {
    fn from_socket_context(context: &SocketContext) -> Self {
        Self {
            netns: context
                .netns
                .as_ref()
                .map(|namespace| namespace.token().to_owned()),
            socket_mark: context.socket_mark,
        }
    }

    fn netns(&self) -> NetNS {
        NetNS::new(self.netns.clone())
    }

    #[cfg(feature = "dns-resolver")]
    fn is_process_default(&self) -> bool {
        self.netns.is_none() && self.socket_mark.is_none() && !native_socket_protection_available()
    }

    #[cfg(feature = "dns-resolver")]
    fn socket_context(&self) -> SocketContext {
        SocketContext::default()
            .with_netns(self.netns.clone().map(NetNamespace::new))
            .with_socket_mark(self.socket_mark)
    }
}

#[cfg(feature = "dns-resolver")]
#[derive(Clone)]
struct RuntimeDnsIoProvider {
    inner: TokioRuntimeProvider,
    context: RuntimeDnsIoContext,
}

#[cfg(feature = "dns-resolver")]
impl RuntimeDnsIoProvider {
    fn new(context: RuntimeDnsIoContext) -> Self {
        Self {
            inner: TokioRuntimeProvider::new(),
            context,
        }
    }
}

#[cfg(feature = "dns-resolver")]
impl RuntimeProvider for RuntimeDnsIoProvider {
    type Handle = <TokioRuntimeProvider as RuntimeProvider>::Handle;
    type Timer = <TokioRuntimeProvider as RuntimeProvider>::Timer;
    type Udp = UdpSocket;
    type Tcp = AsyncIoTokioAsStd<TcpStream>;

    fn create_handle(&self) -> Self::Handle {
        self.inner.create_handle()
    }

    fn connect_tcp(
        &self,
        server_addr: SocketAddr,
        bind_addr: Option<SocketAddr>,
        wait_for: Option<Duration>,
    ) -> Pin<Box<dyn Send + Future<Output = io::Result<Self::Tcp>>>> {
        let options = TcpBindOptions::default()
            .with_context(self.context.socket_context())
            .with_local_addr(bind_addr)
            .with_bind_device(Some(String::new()))
            .with_reuse_addr(false);
        Box::pin(async move {
            let wait_for = wait_for.unwrap_or(Duration::from_secs(5));
            let connect = async {
                let socket = create_tcp_socket(server_addr, &options)
                    .await
                    .map_err(io::Error::other)?;
                socket.set_nodelay(true)?;
                socket.connect(server_addr).await
            };
            match tokio::time::timeout(wait_for, connect).await {
                Ok(Ok(stream)) => Ok(AsyncIoTokioAsStd(stream)),
                Ok(Err(error)) => Err(error),
                Err(_) => Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    format!("connection to {server_addr:?} timed out after {wait_for:?}"),
                )),
            }
        })
    }

    fn bind_udp(
        &self,
        local_addr: SocketAddr,
        _server_addr: SocketAddr,
    ) -> Pin<Box<dyn Send + Future<Output = io::Result<Self::Udp>>>> {
        let options = UdpBindOptions::default()
            .with_context(self.context.socket_context())
            .with_local_addr(Some(local_addr));
        Box::pin(async move { create_udp_socket(&options).await.map_err(io::Error::other) })
    }
}

#[cfg(feature = "dns-resolver")]
type ContextualResolver = Resolver<GenericConnector<RuntimeDnsIoProvider>>;

#[derive(Debug, Default)]
pub(crate) struct RuntimeDnsResolver {
    #[cfg(feature = "dns-resolver")]
    system_dns: SystemDnsResolver,
}

impl RuntimeDnsResolver {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    // A netns token can be deleted and recreated. Keep contextual resolvers
    // request-scoped so pooled DNS sockets cannot outlive that namespace.
    #[cfg(feature = "dns-resolver")]
    fn contextual_resolver(context: RuntimeDnsIoContext) -> ContextualResolver {
        let (config, options) = resolver_config();
        let provider = GenericConnector::new(RuntimeDnsIoProvider::new(context));
        Resolver::builder_with_config(config, provider)
            .with_options(options)
            .build()
    }

    #[cfg(feature = "dns-resolver")]
    async fn resolve_contextual_with_hickory(
        context: RuntimeDnsIoContext,
        host: String,
    ) -> anyhow::Result<Vec<IpAddr>> {
        let resolver = Self::contextual_resolver(context);
        let response = resolver
            .lookup_ip(&host)
            .await
            .with_context(|| format!("contextual hickory lookup_ip failed, host: {host}"))?;
        Ok(response.iter().collect())
    }

    #[cfg(feature = "dns-resolver")]
    async fn resolve_process_ips(&self, host: &str) -> anyhow::Result<Vec<IpAddr>> {
        #[cfg(feature = "doh")]
        if let Some(doh) = current_doh() {
            let resolver_host = host.to_owned();
            let doh_lookup = async {
                let response = RESOLVER
                    .lookup_ip(&resolver_host)
                    .await
                    .with_context(|| format!("DoH lookup_ip failed, host: {resolver_host}"))?;
                Ok::<Vec<IpAddr>, anyhow::Error>(response.iter().collect())
            };
            let fallback_host = host.to_owned();
            let fallback = async move {
                lookup_host((fallback_host.as_str(), 0))
                    .await
                    .map(|addrs| addrs.map(|addr| addr.ip()).collect())
                    .map_err(Into::into)
            };
            return lookup_via_doh_first(Some(&doh), doh_lookup, fallback).await;
        }

        let system_host = host.to_owned();
        self.system_dns
            .resolve(
                async move {
                    let addresses = lookup_host((system_host.as_str(), 0))
                        .await?
                        .map(|address| address.ip())
                        .collect();
                    Ok(addresses)
                },
                async {
                    let response = RESOLVER
                        .lookup_ip(host)
                        .await
                        .with_context(|| format!("hickory dns lookup_ip failed, host: {host}"))?;
                    Ok(response.iter().collect())
                },
            )
            .await
    }

    #[cfg(feature = "dns-resolver")]
    async fn resolve_contextual_ips(
        &self,
        context: RuntimeDnsIoContext,
        host: String,
    ) -> anyhow::Result<Vec<IpAddr>> {
        #[cfg(feature = "doh")]
        if let Some(doh) = current_doh() {
            let doh_lookup = Self::resolve_contextual_with_hickory(context.clone(), host.clone());
            if doh.only {
                return doh_lookup.await;
            }
            match tokio::time::timeout(DOH_LOOKUP_TIMEOUT, doh_lookup).await {
                Ok(Ok(addresses)) => return Ok(addresses),
                Ok(Err(error)) => {
                    tracing::warn!(?error, "contextual doh lookup failed, fallback to system dns")
                }
                Err(_) => {
                    tracing::warn!("contextual doh lookup timed out, fallback to system dns")
                }
            }
            // fall through to the legacy system-first paths below
        }

        if context.socket_mark.is_some() || native_socket_protection_available() {
            return Self::resolve_contextual_with_hickory(context, host).await;
        }

        // libc DNS cannot attach SO_MARK. It remains usable for a
        // namespace-only context when confined to one blocking thread.
        let system_context = context.clone();
        let system_host = host.clone();
        self.system_dns
            .resolve(
                async move {
                    let netns = system_context.netns();
                    let addresses = tokio::task::spawn_blocking(move || {
                        netns.run(|| {
                            (system_host.as_str(), 0)
                                .to_socket_addrs()
                                .map(|addrs| addrs.map(|addr| addr.ip()).collect())
                        })
                    })
                    .await
                    .context("contextual system DNS task failed")??;
                    Ok(addresses)
                },
                Self::resolve_contextual_with_hickory(context, host),
            )
            .await
    }
}

#[async_trait]
impl DnsResolver for RuntimeDnsResolver {
    async fn resolve(&self, query: DnsQuery) -> anyhow::Result<Vec<IpAddr>> {
        let context = RuntimeDnsIoContext::from_socket_context(&query.context);
        #[cfg(feature = "dns-resolver")]
        {
            if context.is_process_default() {
                return self.resolve_process_ips(&query.host).await;
            }
            return self.resolve_contextual_ips(context, query.host).await;
        }
        #[cfg(not(feature = "dns-resolver"))]
        {
            if context.socket_mark.is_some()
                || crate::socket_protector::native_socket_protection_available()
            {
                anyhow::bail!("socket-marked or VPN-protected DNS requires DNS resolver support");
            }
            if context.netns.is_none() {
                return Ok(resolve_ips(&query.host).await?);
            }
            let host = query.host;
            let netns = context.netns();
            return tokio::task::spawn_blocking(move || {
                netns.run(|| {
                    (host.as_str(), 0)
                        .to_socket_addrs()
                        .map(|addrs| addrs.map(|addr| addr.ip()).collect())
                })
            })
            .await
            .context("contextual system DNS task failed")?
            .map_err(Into::into);
        }
    }
}

#[cfg(feature = "dns-resolver")]
#[async_trait]
impl DnsRecordResolver for RuntimeDnsResolver {
    async fn resolve_txt(&self, query: DnsQuery) -> anyhow::Result<String> {
        let context = RuntimeDnsIoContext::from_socket_context(&query.context);
        if context.is_process_default() {
            return Ok(resolve_txt_record(&query.host).await?);
        }

        let resolver = Self::contextual_resolver(context);
        let response = resolver
            .txt_lookup(&query.host)
            .await
            .with_context(|| format!("txt_lookup failed, domain_name: {}", query.host))?;
        let record = response
            .iter()
            .next()
            .with_context(|| format!("no txt record found, domain_name: {}", query.host))?;
        let data = record
            .txt_data()
            .first()
            .with_context(|| format!("empty txt record, domain_name: {}", query.host))?;
        Ok(String::from_utf8_lossy(data).into_owned())
    }

    async fn resolve_srv(&self, query: DnsQuery) -> anyhow::Result<Vec<DnsSrvRecord>> {
        let context = RuntimeDnsIoContext::from_socket_context(&query.context);
        let response = if context.is_process_default() {
            RESOLVER.srv_lookup(&query.host).await?
        } else {
            Self::contextual_resolver(context)
                .srv_lookup(&query.host)
                .await?
        };
        Ok(response
            .iter()
            .map(|record| DnsSrvRecord {
                priority: record.priority(),
                weight: record.weight(),
                port: record.port(),
                target: record.target().to_utf8(),
            })
            .collect())
    }
}

#[cfg(not(feature = "dns-resolver"))]
#[async_trait]
impl DnsRecordResolver for RuntimeDnsResolver {
    async fn resolve_txt(&self, _query: DnsQuery) -> anyhow::Result<String> {
        anyhow::bail!("this build does not include TXT DNS resolution")
    }

    async fn resolve_srv(&self, _query: DnsQuery) -> anyhow::Result<Vec<DnsSrvRecord>> {
        anyhow::bail!("this build does not include SRV DNS resolution")
    }
}

#[cfg(feature = "dns-resolver")]
async fn resolve_txt_record(domain_name: &str) -> Result<String, Error> {
    let r = RESOLVER.clone();
    let response = r
        .txt_lookup(domain_name)
        .await
        .with_context(|| format!("txt_lookup failed, domain_name: {}", domain_name))?;

    let txt_record = response
        .iter()
        .next()
        .with_context(|| format!("no txt record found, domain_name: {}", domain_name))?;

    let txt_data = String::from_utf8_lossy(&txt_record.txt_data()[0]);
    tracing::info!(?txt_data, ?domain_name, "get txt record");

    Ok(txt_data.to_string())
}

pub async fn socket_addrs(
    url: &url::Url,
    default_port_number: impl Fn() -> Option<u16>,
) -> Result<Vec<SocketAddr>, Error> {
    socket_addrs_with_system_resolver(url, default_port_number, true).await
}

async fn socket_addrs_with_system_resolver(
    url: &url::Url,
    default_port_number: impl Fn() -> Option<u16>,
    allow_system_resolver: bool,
) -> Result<Vec<SocketAddr>, Error> {
    let host = url.host().ok_or(Error::InvalidUrl(url.to_string()))?;
    let port = url
        .port()
        .or_else(default_port_number)
        .ok_or(Error::InvalidUrl(url.to_string()))?;

    // if host is an ip address, return it directly
    match host {
        url::Host::Ipv4(ip) => return Ok(vec![SocketAddr::new(std::net::IpAddr::V4(ip), port)]),
        url::Host::Ipv6(ip) => return Ok(vec![SocketAddr::new(std::net::IpAddr::V6(ip), port)]),
        _ => {}
    }
    let host = host.to_string();

    // DNS-over-HTTPS path: plaintext lookups only run as an explicit
    // fallback when doh_only is not set.
    #[cfg(all(feature = "dns-resolver", feature = "doh"))]
    if let Some(doh) = current_doh() {
        let doh_host = host.clone();
        let doh_lookup = async {
            let response = RESOLVER.lookup_ip(&doh_host).await.with_context(|| {
                format!("DoH lookup_ip failed, host: {doh_host}, port: {port}")
            })?;
            Ok::<Vec<IpAddr>, anyhow::Error>(response.iter().collect())
        };
        let fallback_host = host.clone();
        let allow_system = allow_system_resolver;
        let fallback = async move {
            anyhow::ensure!(
                allow_system,
                "system resolver is disabled for this lookup"
            );
            lookup_host(format!("{}:{}", fallback_host, port))
                .await
                .map(|addrs| addrs.map(|addr| addr.ip()).collect())
                .map_err(Into::into)
        };
        return lookup_via_doh_first(Some(&doh), doh_lookup, fallback)
            .await
            .map(|ips| ips.into_iter().map(|ip| SocketAddr::new(ip, port)).collect())
            .map_err(Into::into);
    }

    if allow_system_resolver {
        let socket_addr = format!("{}:{}", host, port);
        match lookup_host(socket_addr).await {
            Ok(a) => {
                let a = a.collect();
                tracing::debug!(?a, "system dns lookup done");
                return Ok(a);
            }
            Err(e) => {
                tracing::error!(?e, "system dns lookup failed");
                #[cfg(not(feature = "dns-resolver"))]
                return Err(e.into());
            }
        }
    }

    // use hickory_resolver
    #[cfg(feature = "dns-resolver")]
    {
        let ret = RESOLVER.lookup_ip(&host).await.with_context(|| {
            format!(
                "hickory dns lookup_ip failed, host: {}, port: {}",
                host, port
            )
        })?;
        Ok(ret
            .iter()
            .map(|ip| SocketAddr::new(ip, port))
            .collect::<Vec<_>>())
    }
    #[cfg(not(feature = "dns-resolver"))]
    unreachable!("the system resolver error returns above")
}

#[cfg(not(feature = "dns-resolver"))]
async fn resolve_ips(host: &str) -> Result<Vec<IpAddr>, Error> {
    Ok(lookup_host((host, 0))
        .await?
        .map(|addr| addr.ip())
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "dns-resolver")]
    #[tokio::test]
    async fn timed_out_system_lookup_is_not_retried() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let resolver = SystemDnsResolver::new(Duration::from_millis(10));
        let system_calls = Arc::new(AtomicUsize::new(0));
        let fallback_calls = AtomicUsize::new(0);
        let expected = vec![IpAddr::V4(std::net::Ipv4Addr::LOCALHOST)];

        let first_system_calls = system_calls.clone();
        let first = resolver
            .resolve(
                async move {
                    first_system_calls.fetch_add(1, Ordering::Relaxed);
                    std::future::pending::<anyhow::Result<Vec<IpAddr>>>().await
                },
                async {
                    fallback_calls.fetch_add(1, Ordering::Relaxed);
                    Ok(expected.clone())
                },
            )
            .await;
        let second_system_calls = system_calls.clone();
        let second = resolver
            .resolve(
                async move {
                    second_system_calls.fetch_add(1, Ordering::Relaxed);
                    std::future::pending::<anyhow::Result<Vec<IpAddr>>>().await
                },
                async {
                    fallback_calls.fetch_add(1, Ordering::Relaxed);
                    Ok(expected.clone())
                },
            )
            .await;

        assert_eq!(first.unwrap(), expected);
        assert_eq!(second.unwrap(), expected);
        assert_eq!(system_calls.load(Ordering::Relaxed), 1);
        assert_eq!(fallback_calls.load(Ordering::Relaxed), 2);
    }

    #[cfg(feature = "dns-resolver")]
    #[tokio::test]
    async fn successful_system_lookup_skips_hickory() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let resolver = SystemDnsResolver::new(Duration::from_millis(10));
        let fallback_calls = AtomicUsize::new(0);
        let expected = vec![IpAddr::V4(std::net::Ipv4Addr::LOCALHOST)];
        let system_result = expected.clone();

        let addresses = resolver
            .resolve(async move { Ok(system_result) }, async {
                fallback_calls.fetch_add(1, Ordering::Relaxed);
                Ok(Vec::new())
            })
            .await
            .unwrap();

        assert_eq!(addresses, expected);
        assert_eq!(fallback_calls.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn runtime_dns_context_preserves_process_routing_inputs() {
        let context = SocketContext::default()
            .with_socket_mark(Some(0))
            .with_netns(Some(easytier_core::socket::NetNamespace::new("instance-a")));

        assert_eq!(
            RuntimeDnsIoContext::from_socket_context(&context),
            RuntimeDnsIoContext {
                netns: Some("instance-a".to_owned()),
                socket_mark: Some(0),
            }
        );
    }

    #[tokio::test]
    async fn test_socket_addrs() {
        let url = url::Url::parse("tcp://github-ci-test.easytier.cn:80").unwrap();
        let addrs = socket_addrs(&url, || Some(80)).await.unwrap();
        assert_eq!(2, addrs.len(), "addrs: {:?}", addrs);
        println!("addrs: {:?}", addrs);

        let addrs = socket_addrs_with_system_resolver(&url, || Some(80), false)
            .await
            .unwrap();
        assert_eq!(2, addrs.len(), "addrs: {:?}", addrs);
        println!("addrs2: {:?}", addrs);
    }

    #[tokio::test]
    async fn socket_addrs_preserves_explicit_zero_port() {
        let cases = [
            ("ws://127.0.0.1:0", 80, 0),
            ("wss://127.0.0.1:0", 443, 0),
            ("ws://127.0.0.1", 80, 80),
            ("wss://127.0.0.1", 443, 443),
        ];

        for (raw_url, default_port, expected_port) in cases {
            let url = url::Url::parse(raw_url).unwrap();
            let addrs = socket_addrs(&url, || Some(default_port)).await.unwrap();
            assert_eq!(
                addrs,
                vec![SocketAddr::from(([127, 0, 0, 1], expected_port))]
            );
        }
    }
}

#[cfg(all(test, feature = "doh"))]
mod doh_tests {
    use super::*;
    use futures_util::FutureExt as _;

    fn ip(s: &str) -> IpAddr {
        s.parse().unwrap()
    }

    fn prefer_config(url: &str, bootstrap: Option<IpAddr>) -> DohServerConfig {
        resolve_doh_config(&DohSettings {
            url: url.to_owned(),
            bootstrap_ip: bootstrap,
            tls_name: None,
            only: false,
            ca_cert_path: None,
        })
        .now_or_never()
        .unwrap()
        .unwrap()
    }

    fn only_config(url: &str, bootstrap: Option<IpAddr>) -> DohServerConfig {
        resolve_doh_config(&DohSettings {
            url: url.to_owned(),
            bootstrap_ip: bootstrap,
            tls_name: None,
            only: true,
            ca_cert_path: None,
        })
        .now_or_never()
        .unwrap()
        .unwrap()
    }

    #[test]
    fn parses_ip_host_doh_url() {
        let name_server = build_doh_name_server("https://1.1.1.1/dns-query", None, None).unwrap();
        assert_eq!(name_server.socket_addr, "1.1.1.1:443".parse().unwrap());
        assert_eq!(name_server.protocol, Protocol::Https);
        assert_eq!(name_server.tls_dns_name.as_deref(), Some("1.1.1.1"));
        assert_eq!(name_server.http_endpoint.as_deref(), Some("/dns-query"));
    }

    #[test]
    fn parses_domain_with_bootstrap_and_custom_port_path() {
        let name_server = build_doh_name_server(
            "https://dns.google:8443/custom-dns",
            Some(ip("8.8.8.8")),
            None,
        )
        .unwrap();
        assert_eq!(name_server.socket_addr, "8.8.8.8:8443".parse().unwrap());
        assert_eq!(name_server.protocol, Protocol::Https);
        assert_eq!(name_server.tls_dns_name.as_deref(), Some("dns.google"));
        assert_eq!(name_server.http_endpoint.as_deref(), Some("/custom-dns"));
    }

    #[test]
    fn tls_name_override_wins_over_host() {
        let name_server =
            build_doh_name_server("https://1.1.1.1/dns-query", None, Some("cloudflare-dns.com"))
                .unwrap();
        assert_eq!(name_server.tls_dns_name.as_deref(), Some("cloudflare-dns.com"));
        assert_eq!(name_server.socket_addr, "1.1.1.1:443".parse().unwrap());
    }

    #[test]
    fn rejects_non_https_scheme() {
        assert!(build_doh_name_server("http://1.1.1.1/dns-query", None, None).is_err());
    }

    #[test]
    fn rejects_query_string_in_url() {
        assert!(build_doh_name_server("https://1.1.1.1/dns-query?extra=1", None, None).is_err());
    }

    #[test]
    fn domain_without_bootstrap_is_rejected() {
        assert!(build_doh_name_server("https://dns.google/dns-query", None, None).is_err());
    }

    #[tokio::test]
    async fn only_mode_domain_requires_bootstrap() {
        let error = resolve_doh_config(&DohSettings {
            url: "https://dns.google/dns-query".to_owned(),
            bootstrap_ip: None,
            tls_name: None,
            only: true,
            ca_cert_path: None,
        })
        .await
        .unwrap_err();
        assert!(error.to_string().contains("bootstrap"), "error: {error}");
    }

    #[tokio::test]
    async fn ip_host_needs_no_bootstrap_even_in_only_mode() {
        let config = only_config("https://1.1.1.1/dns-query", None);
        assert_eq!(config.name_server.socket_addr, "1.1.1.1:443".parse().unwrap());
        assert!(config.only);
    }

    #[test]
    fn only_resolver_config_has_no_plaintext_name_servers() {
        let config = only_config("https://1.1.1.1/dns-query", None);
        let (resolver_config, _) = resolver_config_with(Some(&config));
        let name_servers = resolver_config.name_servers();
        assert_eq!(name_servers.len(), 1, "name_servers: {name_servers:?}");
        assert_eq!(name_servers[0].protocol, Protocol::Https);
    }

    #[test]
    fn prefer_resolver_config_keeps_plaintext_fallback_after_doh() {
        let config = prefer_config("https://1.1.1.1/dns-query", None);
        let (resolver_config, _) = resolver_config_with(Some(&config));
        let name_servers = resolver_config.name_servers();
        assert!(name_servers.len() >= 2, "name_servers: {name_servers:?}");
        assert_eq!(name_servers[0].protocol, Protocol::Https);
        assert!(name_servers[1..].iter().any(|ns| ns.protocol == Protocol::Udp));
    }

    #[test]
    fn resolver_config_without_doh_matches_legacy_behavior() {
        let (resolver_config, _) = resolver_config_with(None);
        assert!(!resolver_config.name_servers().is_empty());
        assert!(resolver_config
            .name_servers()
            .iter()
            .all(|ns| ns.protocol != Protocol::Https));
    }

    #[tokio::test]
    async fn doh_failure_falls_back_when_prefer() {
        let config = prefer_config("https://1.1.1.1/dns-query", None);
        let result = lookup_via_doh_first_with_timeout(
            &config,
            Duration::from_millis(50),
            async { anyhow::bail!("DoH server unreachable") },
            async { Ok(vec![ip("127.0.0.1")]) },
        )
        .await
        .unwrap();
        assert_eq!(result, vec![ip("127.0.0.1")]);
    }

    #[tokio::test]
    async fn doh_failure_bails_when_only() {
        let config = only_config("https://1.1.1.1/dns-query", None);
        let result = lookup_via_doh_first_with_timeout(
            &config,
            Duration::from_millis(50),
            async { anyhow::bail!("DoH server unreachable") },
            async { Ok(vec![ip("127.0.0.1")]) },
        )
        .await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn doh_success_skips_plaintext_fallback() {
        let config = prefer_config("https://1.1.1.1/dns-query", None);
        let result = lookup_via_doh_first_with_timeout(
            &config,
            Duration::from_millis(50),
            async { Ok(vec![ip("192.0.2.1")]) },
            async { anyhow::bail!("plaintext fallback must not be called") },
        )
        .await
        .unwrap();
        assert_eq!(result, vec![ip("192.0.2.1")]);
    }

    #[tokio::test]
    async fn doh_timeout_falls_back_when_prefer() {
        let config = prefer_config("https://1.1.1.1/dns-query", None);
        let result = lookup_via_doh_first_with_timeout(
            &config,
            Duration::from_millis(10),
            std::future::pending(),
            async { Ok(vec![ip("127.0.0.2")]) },
        )
        .await
        .unwrap();
        assert_eq!(result, vec![ip("127.0.0.2")]);
    }

    #[tokio::test]
    async fn doh_timeout_bails_when_only() {
        let config = only_config("https://1.1.1.1/dns-query", None);
        let result = lookup_via_doh_first_with_timeout(
            &config,
            Duration::from_millis(10),
            std::future::pending(),
            async { Ok(vec![ip("127.0.0.2")]) },
        )
        .await;
        assert!(result.is_err());
    }

    #[cfg(feature = "websocket")]
    #[test]
    fn parses_pem_ca_chain() {
        let pem = generate_test_cert_pem();
        let ca_file = tempfile::Builder::new().suffix(".pem").tempfile().unwrap();
        std::fs::write(ca_file.path(), &pem).unwrap();
        let certs = parse_pem_certs(ca_file.path().to_str().unwrap()).unwrap();
        assert_eq!(certs.len(), 1);

        std::fs::write(ca_file.path(), "not a pem").unwrap();
        assert!(parse_pem_certs(ca_file.path().to_str().unwrap()).is_err());
    }

    #[cfg(feature = "websocket")]
    #[test]
    fn tls_config_accepts_custom_ca_and_webpki_default() {
        let mut config = prefer_config("https://1.1.1.1/dns-query", None);
        config.ca_certs_der = parse_pem_to_der(generate_test_cert_pem());
        let _tls_with_ca = config.tls_client_config();

        config.ca_certs_der.clear();
        let _tls_with_webpki = config.tls_client_config();
    }

    #[cfg(feature = "websocket")]
    fn generate_test_cert_pem() -> String {
        let params = rcgen::CertificateParams::new(vec!["localhost".to_owned()]);
        rcgen::Certificate::from_params(params)
            .unwrap()
            .serialize_pem()
            .unwrap()
    }

    fn parse_pem_to_der(pem: String) -> Vec<Vec<u8>> {
        let ca_file = tempfile::Builder::new().suffix(".pem").tempfile().unwrap();
        std::fs::write(ca_file.path(), pem).unwrap();
        parse_pem_certs(ca_file.path().to_str().unwrap())
            .unwrap()
            .into_iter()
            .map(|cert| cert.to_vec())
            .collect()
    }
    #[test]
    fn parses_ipv6_literal_doh_url() {
        let name_server =
            build_doh_name_server("https://[2606:4700:4700::1111]/dns-query", None, None).unwrap();
        assert_eq!(
            name_server.socket_addr,
            "[2606:4700:4700::1111]:443".parse().unwrap()
        );
        assert_eq!(name_server.protocol, Protocol::Https);
        // no brackets in the tls name so rustls parses it as an IP server name
        assert_eq!(
            name_server.tls_dns_name.as_deref(),
            Some("2606:4700:4700::1111")
        );
        assert_eq!(name_server.http_endpoint.as_deref(), Some("/dns-query"));
    }

    #[tokio::test]
    async fn ipv6_literal_needs_no_bootstrap_even_in_only_mode() {
        let config = only_config("https://[2606:4700:4700::1111]/dns-query", None);
        assert_eq!(
            config.name_server.socket_addr,
            "[2606:4700:4700::1111]:443".parse().unwrap()
        );
        assert!(config.only);
    }

    #[test]
    fn domain_with_ipv6_bootstrap_resolves_to_v6_socket() {
        let name_server = build_doh_name_server(
            "https://dns.google/dns-query",
            Some(ip("2001:4860:4860::8888")),
            None,
        )
        .unwrap();
        assert_eq!(
            name_server.socket_addr,
            "[2001:4860:4860::8888]:443".parse().unwrap()
        );
        assert_eq!(name_server.tls_dns_name.as_deref(), Some("dns.google"));
    }
}

#[cfg(all(test, feature = "doh", feature = "websocket"))]
mod doh_e2e_tests {
    use super::*;

    /// Runs a real TLS + HTTP/2 DoH server on a loopback port, answering
    /// every A query with 192.0.2.1. Returns the port and the CA PEM temp
    /// file the client must trust.
    async fn spawn_local_doh_server() -> (u16, tempfile::TempPath) {
        let mut params = rcgen::CertificateParams::new(vec!["localhost".to_owned()]);
        params
            .subject_alt_names
            .push(rcgen::SanType::IpAddress("127.0.0.1".parse().unwrap()));
        let cert = rcgen::Certificate::from_params(params).unwrap();
        let cert_pem = cert.serialize_pem().unwrap();
        let cert_der = cert.serialize_der().unwrap();
        let key_der = cert.get_key_pair().serialize_der();

        let mut ca_file = tempfile::Builder::new().suffix(".pem").tempfile().unwrap();
        std::io::Write::write_all(&mut ca_file, cert_pem.as_bytes()).unwrap();
        let ca_path = ca_file.into_temp_path();

        let server_config = rustls::ServerConfig::builder_with_provider(Arc::new(
            rustls::crypto::ring::default_provider(),
        ))
        .with_safe_default_protocol_versions()
        .unwrap()
        .with_no_client_auth()
        .with_single_cert(
            vec![rustls::pki_types::CertificateDer::from(cert_der)],
            rustls::pki_types::PrivatePkcs8KeyDer::from(key_der).into(),
        )
        .unwrap();
        let mut server_config = server_config;
        server_config.alpn_protocols = vec![b"h2".to_vec()];
        let acceptor = tokio_rustls::TlsAcceptor::from(Arc::new(server_config));

        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();

        tokio::spawn(async move {
            while let Ok((tcp, _)) = listener.accept().await {
                let acceptor = acceptor.clone();
                tokio::spawn(async move {
                    if let Ok(tls) = acceptor.accept(tcp).await {
                        serve_doh_over_h2(tls).await;
                    }
                });
            }
        });

        (port, ca_path)
    }

    async fn serve_doh_over_h2<S>(tls: S)
    where
        S: tokio::io::AsyncRead + tokio::io::AsyncWrite + Unpin + Send,
    {
        let mut conn = match h2::server::handshake(tls).await {
            Ok(conn) => conn,
            Err(_) => return,
        };
        while let Some(accepted) = conn.accept().await {
            let (request, mut respond) = match accepted {
                Ok(accepted) => accepted,
                Err(_) => return,
            };
            let (_, mut body) = request.into_parts();
            let mut query = Vec::new();
            while let Some(chunk) = body.data().await {
                match chunk {
                    Ok(chunk) => {
                        let _ = body.flow_control().release_capacity(chunk.len());
                        query.extend_from_slice(&chunk);
                    }
                    Err(_) => break,
                }
            }
            let response_bytes = build_doh_response(&query);
            let http_response = http::Response::builder()
                .status(200)
                .header("content-type", "application/dns-message")
                .body(())
                .unwrap();
            if let Ok(mut send) = respond.send_response(http_response, false) {
                let _ = send.send_data(response_bytes.into(), true);
            }
        }
    }

    fn build_doh_response(query: &[u8]) -> Vec<u8> {
        use hickory_proto::op::{Message, MessageType, OpCode, ResponseCode};
        use hickory_proto::rr::rdata::A;
        use hickory_proto::rr::{RData, Record, RecordType};

        let request = Message::from_vec(query).expect("valid dns query");
        let q = request.queries().first().expect("query present").clone();
        let mut response = Message::new();
        response.set_id(request.id());
        response.set_message_type(MessageType::Response);
        response.set_op_code(OpCode::Query);
        response.set_response_code(ResponseCode::NoError);
        // hickory only trusts empty/negative answers from authoritative servers
        response.set_authoritative(true);
        response.add_query(q.clone());
        if q.query_type() == RecordType::A {
            response.add_answer(Record::from_rdata(
                q.name().clone(),
                60,
                RData::A(A::from(std::net::Ipv4Addr::new(192, 0, 2, 1))),
            ));
        }
        response.to_vec().expect("serialize dns response")
    }

    #[tokio::test]
    async fn resolves_through_local_tls_h2_doh_server() {
        let (port, ca_path) = spawn_local_doh_server().await;

        let settings = DohSettings {
            url: format!("https://127.0.0.1:{port}/dns-query"),
            bootstrap_ip: None,
            tls_name: None,
            // only=true so the test cannot silently leak to plaintext servers
            only: true,
            ca_cert_path: Some(ca_path.to_string_lossy().to_string()),
        };
        let config = resolve_doh_config(&settings).await.unwrap();
        let resolver = build_resolver(Some(&config));
        let ips: Vec<IpAddr> = resolver
            .lookup_ip("doh-test.example.com")
            .await
            .expect("DoH lookup over local TLS+H2 server")
            .iter()
            .collect();
        assert!(
            ips.contains(&"192.0.2.1".parse::<IpAddr>().unwrap()),
            "ips: {ips:?}"
        );
    }

    #[tokio::test]
    async fn only_mode_never_falls_back_to_plaintext() {
        // closed loopback port: the DoH connection is refused instantly
        let settings = DohSettings {
            url: "https://127.0.0.1:1/dns-query".to_owned(),
            bootstrap_ip: None,
            tls_name: None,
            only: true,
            ca_cert_path: None,
        };
        let config = resolve_doh_config(&settings).await.unwrap();
        let resolver = build_resolver(Some(&config));
        let result = lookup_via_doh_first(
            Some(&config),
            async {
                let response = resolver.lookup_ip("doh-test.example.com").await?;
                Ok::<_, anyhow::Error>(response.iter().collect::<Vec<IpAddr>>())
            },
            async { panic!("plaintext fallback must not run in only mode") },
        )
        .await;
        assert!(result.is_err(), "only mode must fail when DoH is down");
    }
}
