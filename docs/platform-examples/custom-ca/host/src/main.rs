//! Probe: a minimal wasmtime embedder that runs a `wasi:cli/command` component with `wasi:http`,
//! and verifies HTTPS servers against a CA bundle it is given (a cluster CA) instead of the
//! compiled-in public roots that `wasmtime run -S http` uses.
//!
//!   ca-host <ca.pem> <component.wasm> <dir-to-preopen-as-/pki> [component args...]
//!
//! The only customization is `WasiHttpHooks::send_request`; everything else is wasmtime's.

use http_body_util::BodyExt;
use rustls_pki_types::pem::PemObject;
use rustls_pki_types::{CertificateDer, ServerName};
use std::sync::Arc;
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Config, Engine, Store};
use wasmtime_wasi::p2::bindings::Command;
use wasmtime_wasi::{FsPerms, WasiCtx, WasiCtxView, WasiView};
use wasmtime_wasi_http::io::TokioIo;
use wasmtime_wasi_http::{
    Error, RequestOptions, Result as HttpResult, WasiBody, WasiHttpCtx, WasiHttpCtxView, WasiHttpHooks, WasiHttpView,
};

/// The TLS client configuration: roots from the given CA bundle only.
struct CaHooks {
    tls: Arc<rustls::ClientConfig>,
}

impl WasiHttpHooks for CaHooks {
    fn send_request(
        &mut self,
        mut req: http::Request<WasiBody>,
        _options: Option<RequestOptions>,
        _fut: Box<dyn Future<Output = Result<(), Error>> + Send>,
    ) -> Box<
        dyn Future<
                Output = HttpResult<(
                    http::Response<WasiBody>,
                    Box<dyn Future<Output = Result<(), Error>> + Send>,
                )>,
            > + Send,
    > {
        let tls = self.tls.clone();
        Box::new(async move {
            let uri = req.uri().clone();
            let host = uri.host().ok_or(Error::HttpRequestUriInvalid)?.to_string();
            let https = uri.scheme_str() == Some("https");
            let port = uri.port_u16().unwrap_or(if https { 443 } else { 80 });
            let tcp = tokio::net::TcpStream::connect((host.as_str(), port))
                .await
                .map_err(Error::Connect)?;
            // Origin-form request target, as `default_send_request` does.
            *req.uri_mut() = http::Uri::builder()
                .path_and_query(uri.path_and_query().map(|p| p.as_str()).unwrap_or("/"))
                .build()
                .unwrap();
            let (mut sender, conn) = if https {
                let name = ServerName::try_from(host).map_err(|_| Error::HttpRequestUriInvalid)?;
                let stream = tokio_rustls::TlsConnector::from(tls)
                    .connect(name, tcp)
                    .await
                    .map_err(Error::Tls)?;
                let (s, c) = hyper::client::conn::http1::handshake(TokioIo::new(stream)).await?;
                tokio::spawn(async move {
                    let _ = c.await;
                });
                (s, ())
            } else {
                let (s, c) = hyper::client::conn::http1::handshake(TokioIo::new(tcp)).await?;
                tokio::spawn(async move {
                    let _ = c.await;
                });
                (s, ())
            };
            let () = conn;
            let res = sender.send_request(req).await?;
            let res = res.map(|b| b.map_err(Error::from).boxed_unsync());
            let io: Box<dyn Future<Output = Result<(), Error>> + Send> = Box::new(async { Ok(()) });
            Ok((res, io))
        })
    }
}

struct Host {
    table: ResourceTable,
    wasi: WasiCtx,
    http: WasiHttpCtx,
    hooks: CaHooks,
}

impl WasiView for Host {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView { ctx: &mut self.wasi, table: &mut self.table }
    }
}

impl WasiHttpView for Host {
    fn http(&mut self) -> WasiHttpCtxView<'_> {
        WasiHttpCtxView { ctx: &mut self.http, table: &mut self.table, hooks: &mut self.hooks }
    }
}

#[tokio::main]
async fn main() -> wasmtime::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let (ca, wasm, dir) = (&args[1], &args[2], &args[3]);

    let mut roots = rustls::RootCertStore::empty();
    for cert in CertificateDer::pem_file_iter(ca).expect("read CA bundle") {
        roots.add(cert.expect("parse CA certificate")).expect("add CA certificate");
    }
    let tls = rustls::ClientConfig::builder_with_provider(Arc::new(
        rustls::crypto::ring::default_provider(),
    ))
    .with_safe_default_protocol_versions()
    .unwrap()
    .with_root_certificates(roots)
    .with_no_client_auth();

    let mut config = Config::new();
    config.wasm_tail_call(true); // our backend emits `return_call`
    let engine = Engine::new(&config)?;
    let component = Component::from_file(&engine, wasm)?;
    let mut linker: Linker<Host> = Linker::new(&engine);
    wasmtime_wasi::p2::add_to_linker_async(&mut linker)?;
    wasmtime_wasi_http::p2::add_only_http_to_linker_async(&mut linker)?;

    let mut guest_args = vec![wasm.clone()];
    guest_args.extend(args[4..].iter().cloned());
    let wasi = WasiCtx::builder()
        .inherit_stdio()
        .args(&guest_args)
        .preopened_dir(dir, "/pki", FsPerms::ReadOnly)?
        .build();
    let host = Host {
        table: ResourceTable::new(),
        wasi,
        http: WasiHttpCtx::new(),
        hooks: CaHooks { tls: Arc::new(tls) },
    };
    let mut store = Store::new(&engine, host);
    let command = Command::instantiate_async(&mut store, &component, &linker).await?;
    let ok = command.wasi_cli_run().call_run(&mut store).await?;
    std::process::exit(if ok.is_ok() { 0 } else { 1 });
}
