//! The Memcached operator in Rust with kube-rs, for comparison with `operator.bc`.
//!
//! Written for this comparison and not compiled here. It follows the operator-sdk tutorial's
//! behaviour and kube-rs's own examples, using only APIs checked against kube-rs `main` (the
//! `kube` 4.x line that `kube-rs/controller-rs` depends on):
//!   - `examples/configmapgen_controller.rs`: `Controller::new(..).owns(..).with_config(
//!     Config::default().concurrency(2)).shutdown_on_signal().run(reconcile, error_policy, ctx)`,
//!     `Patch::Apply` with `PatchParams::apply(..)`, `Action::requeue`;
//!   - `examples/secret_syncer.rs` and `kube-runtime/src/finalizer.rs`: `finalizer(&api, NAME,
//!     obj, |event| async { match event { Event::Apply(o) => .., Event::Cleanup(o) => .. } })`;
//!   - `kube-rs/controller-rs` `src/controller.rs`: `patch_status`, `PatchParams::apply(..)
//!     .force()`, the error policy, `Recorder`; `src/fixtures.rs`: the mock API server
//!     (`tower_test::mock::pair`, `Client::new(mock_service, "default")`);
//!   - leader election is not in kube-runtime; `kube-lease-manager` (0.12) is the usual crate:
//!     `LeaseManagerBuilder::new(client, name).build().await?`, `manager.watch().await`.
//!
//! `// COLOR:` marks each place where function colouring (async/sync, fallible/infallible,
//! Stream/Iterator) shows in the code. README §2 discusses them.

use futures::{StreamExt, TryStreamExt};
use k8s_openapi::api::apps::v1::{Deployment, DeploymentSpec};
use k8s_openapi::api::core::v1::{Container, ContainerPort, PodSpec, PodTemplateSpec};
use k8s_openapi::apimachinery::pkg::apis::meta::v1::{Condition, LabelSelector, Time};
use kube::{
    api::{Api, ObjectMeta, Patch, PatchParams, ResourceExt},
    runtime::{
        controller::{Action, Config as CtrlConfig, Controller},
        events::{Event as KEvent, EventType, Recorder, Reporter},
        finalizer::{finalizer, Event as Finalizer},
        watcher,
    },
    Client, CustomResource, Resource,
};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::{collections::BTreeMap, sync::Arc, time::Duration};
use thiserror::Error;
use tracing::{info, instrument, warn};

// ---------------------------------------------------------------------------------------------
// The custom resource
// ---------------------------------------------------------------------------------------------

#[derive(CustomResource, Deserialize, Serialize, Clone, Debug, JsonSchema)]
#[kube(group = "cache.example.com", version = "v1alpha1", kind = "Memcached", namespaced)]
#[kube(status = "MemcachedStatus")]
#[serde(rename_all = "camelCase")]
pub struct MemcachedSpec {
    pub size: i32,
    pub container_port: i32,
}

#[derive(Deserialize, Serialize, Clone, Default, Debug, JsonSchema)]
pub struct MemcachedStatus {
    pub conditions: Vec<Condition>,
}

const FINALIZER: &str = "cache.example.com/finalizer";
const MANAGER: &str = "memcached-operator";

#[derive(Debug, Error)]
pub enum Error {
    #[error("kube: {0}")]
    Kube(#[from] kube::Error),
    #[error("finalizer: {0}")]
    Finalizer(#[source] Box<kube::runtime::finalizer::Error<Error>>),
    #[error("invalid spec: {0}")]
    Invalid(String),
    #[error("timed out")]
    Timeout,
}

// COLOR: the context is shared by concurrent reconciles, so it is `Arc`-wrapped and every field
// must be `Send + Sync`; the reconciler future must be `Send + 'static`, so it cannot borrow
// from `main`.
pub struct Ctx {
    pub client: Client,
    pub recorder: Recorder,
    pub image: String,
    pub request_timeout: Duration,
}

// ---------------------------------------------------------------------------------------------
// Retry and timeout
// ---------------------------------------------------------------------------------------------

// COLOR: two retry helpers would be needed to serve sync and async callers; this is the async
// one. The body is a closure returning a future (`FnMut() -> Fut`), because an `async` closure
// that borrows its environment across retries does not fit `FnMut` without care. A sync caller
// cannot use it; a caller of a `Stream` needs a third shape.
async fn retry<T, F, Fut>(timeout: Duration, mut body: F) -> Result<T, Error>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T, kube::Error>>,
{
    let mut delay = Duration::from_millis(100);
    for attempt in 0.. {
        // COLOR: `tokio::time::timeout` exists only for futures; a sync call cannot be timed out.
        let r = match tokio::time::timeout(timeout, body()).await {
            Ok(r) => r.map_err(Error::Kube),
            Err(_) => Err(Error::Timeout),
        };
        match r {
            Ok(v) => return Ok(v),
            Err(e) if attempt < 3 && is_transient(&e) => {
                tokio::time::sleep(delay).await; // COLOR: tokio's clock; mockable only via `pause()`
                delay = (delay * 2).min(Duration::from_secs(5));
            }
            Err(e) => return Err(e),
        }
    }
    unreachable!()
}

fn is_transient(e: &Error) -> bool {
    match e {
        Error::Timeout => true,
        Error::Kube(kube::Error::Api(s)) => s.code == 429 || s.code >= 500,
        Error::Kube(kube::Error::HyperError(_)) | Error::Kube(kube::Error::Service(_)) => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------------------------
// Desired state (pure)
// ---------------------------------------------------------------------------------------------

fn labels(image: &str) -> BTreeMap<String, String> {
    let tag = image.split_once(':').map(|(_, t)| t).unwrap_or("latest");
    BTreeMap::from([
        ("app.kubernetes.io/name".into(), "memcached-operator".into()),
        ("app.kubernetes.io/version".into(), tag.into()),
        ("app.kubernetes.io/managed-by".into(), "MemcachedController".into()),
    ])
}

// Owned strings throughout: k8s-openapi's types own their fields, so building the Deployment
// clones every string it takes from the custom resource.
fn desired(mc: &Memcached, image: &str) -> Deployment {
    let ls = labels(image);
    Deployment {
        metadata: ObjectMeta {
            name: Some(mc.name_any()),
            namespace: mc.namespace(),
            owner_references: Some(vec![mc.controller_owner_ref(&()).unwrap()]),
            ..Default::default()
        },
        spec: Some(DeploymentSpec {
            replicas: Some(mc.spec.size),
            selector: LabelSelector { match_labels: Some(ls.clone()), ..Default::default() },
            template: PodTemplateSpec {
                metadata: Some(ObjectMeta { labels: Some(ls), ..Default::default() }),
                spec: Some(PodSpec {
                    containers: vec![Container {
                        name: "memcached".into(),
                        image: Some(image.into()),
                        image_pull_policy: Some("IfNotPresent".into()),
                        ports: Some(vec![ContainerPort {
                            container_port: mc.spec.container_port,
                            name: Some("memcached".into()),
                            ..Default::default()
                        }]),
                        command: Some(vec!["memcached".into(), "-m=64".into(), "-o".into(), "modern".into(), "-v".into()]),
                        ..Default::default()
                    }],
                    ..Default::default()
                }),
            },
            ..Default::default()
        }),
        ..Default::default()
    }
}

fn set_condition(conds: &mut Vec<Condition>, mut c: Condition) {
    if let Some(old) = conds.iter().find(|x| x.type_ == c.type_) {
        if old.status == c.status {
            c.last_transition_time = old.last_transition_time.clone();
        }
    }
    conds.retain(|x| x.type_ != c.type_);
    conds.push(c);
}

fn condition(type_: &str, status: &str, reason: &str, message: String, mc: &Memcached) -> Condition {
    Condition {
        type_: type_.into(),
        status: status.into(),
        reason: reason.into(),
        message,
        last_transition_time: Time(jiff::Timestamp::now()),
        observed_generation: mc.metadata.generation,
    }
}

// ---------------------------------------------------------------------------------------------
// Reconcile
// ---------------------------------------------------------------------------------------------

// COLOR: `async fn`. Every function it calls that talks to the API server is async too, and so
// is every function that calls one of those. A sync caller (a CLI, a unit test without a
// runtime) cannot call it; it must be driven by an executor.
#[instrument(skip(mc, ctx), fields(name = %mc.name_any(), ns = ?mc.namespace()))]
async fn reconcile(mc: Arc<Memcached>, ctx: Arc<Ctx>) -> Result<Action, Error> {
    let ns = mc.namespace().unwrap();
    let api: Api<Memcached> = Api::namespaced(ctx.client.clone(), &ns);
    if !(1..=3).contains(&mc.spec.size) {
        return Err(Error::Invalid(format!("size {} out of range", mc.spec.size)));
    }
    // COLOR: the finalizer helper takes an async closure; its error type wraps ours, so the
    // result is `.map_err`ed again.
    finalizer(&api, FINALIZER, mc, |event| async {
        match event {
            Finalizer::Apply(mc) => apply(mc, ctx.clone()).await,
            Finalizer::Cleanup(mc) => cleanup(mc, ctx.clone()).await,
        }
    })
    .await
    .map_err(|e| Error::Finalizer(Box::new(e)))
}

async fn apply(mc: Arc<Memcached>, ctx: Arc<Ctx>) -> Result<Action, Error> {
    let ns = mc.namespace().unwrap();
    let name = mc.name_any();
    let deps: Api<Deployment> = Api::namespaced(ctx.client.clone(), &ns);
    let mcs: Api<Memcached> = Api::namespaced(ctx.client.clone(), &ns);

    // COLOR: `.await` and `?` on every call. Each call is wrapped in a closure that returns a
    // future so that `retry` can call it again.
    let have = retry(ctx.request_timeout, || deps.get_opt(&name)).await?;
    let want = desired(&mc, &ctx.image);
    let pp = PatchParams::apply(MANAGER).force();
    retry(ctx.request_timeout, || deps.patch(&name, &pp, &Patch::Apply(&want))).await?;

    let ready = have
        .and_then(|d| d.status)
        .and_then(|s| s.ready_replicas)
        .unwrap_or(0);
    let mut conds = mc.status.clone().unwrap_or_default().conditions;
    let c = if ready == mc.spec.size {
        condition("Available", "True", "Reconciled", format!("{ready} replicas ready"), &mc)
    } else {
        condition("Available", "False", "Scaling", format!("{ready} of {} replicas ready", mc.spec.size), &mc)
    };
    set_condition(&mut conds, c);
    let status = Patch::Apply(json!({
        "apiVersion": "cache.example.com/v1alpha1",
        "kind": "Memcached",
        "status": { "conditions": conds },
    }));
    retry(ctx.request_timeout, || mcs.patch_status(&name, &pp, &status)).await?;
    info!(ready, "reconciled");
    Ok(if ready == mc.spec.size { Action::requeue(Duration::from_secs(300)) } else { Action::requeue(Duration::from_secs(15)) })
}

async fn cleanup(mc: Arc<Memcached>, ctx: Arc<Ctx>) -> Result<Action, Error> {
    let ev = KEvent {
        type_: EventType::Warning,
        reason: "Deleting".into(),
        note: Some(format!("Custom Resource {} is being deleted from the namespace {}", mc.name_any(), mc.namespace().unwrap())),
        action: "Deleting".into(),
        secondary: None,
    };
    ctx.recorder.publish(&ev, &mc.object_ref(&())).await?;
    Ok(Action::await_change())
}

// COLOR: the error policy is a separate, *sync* callback: it cannot log through an async sink or
// update anything that needs `.await`.
fn error_policy(_mc: Arc<Memcached>, err: &Error, _ctx: Arc<Ctx>) -> Action {
    warn!(error = %err, "reconcile failed");
    Action::requeue(Duration::from_secs(5))
}

// ---------------------------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------------------------

#[tokio::main] // COLOR: the runtime is chosen here and every caller below is tied to it
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt().json().init(); // ambient: a global subscriber, not in any type
    let image = std::env::var("MEMCACHED_IMAGE")?;
    let concurrency: u16 = std::env::var("CONCURRENCY").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let client = Client::try_default().await?;
    let ctx = Arc::new(Ctx {
        client: client.clone(),
        recorder: Recorder::new(client.clone(), Reporter::from(MANAGER)),
        image,
        request_timeout: Duration::from_secs(10),
    });

    // Leader election: `kube-lease-manager`. Waiting for the lock is a channel; losing it must be
    // wired to the controller's shutdown by hand (omitted: `graceful_shutdown_on(..)` with a
    // future that resolves when the channel reports `false`).
    let manager = kube_lease_manager::LeaseManagerBuilder::new(client.clone(), "memcached-operator")
        .build()
        .await?;
    let (mut leader, _lease_task) = manager.watch().await;
    while !*leader.borrow_and_update() {
        leader.changed().await?;
    }

    // COLOR: `Controller::run` returns a `Stream`, consumed with `StreamExt::for_each` and an
    // async closure; the same pipeline over an `Iterator` would be a different trait.
    Controller::new(Api::<Memcached>::all(client.clone()), watcher::Config::default())
        .owns(Api::<Deployment>::all(client), watcher::Config::default())
        .with_config(CtrlConfig::default().concurrency(concurrency))
        .shutdown_on_signal()
        .run(reconcile, error_policy, ctx)
        .for_each(|res| async move {
            match res {
                Ok((obj, _)) => info!(%obj, "reconciled"),
                Err(e) => warn!(error = %e, "reconcile failed"),
            }
        })
        .await;
    Ok(())
}

// A raw watch outside the controller, to show where serde meets async I/O.
// COLOR: `Api::watch` returns a `Stream` of already-decoded events (kube buffers each line and
// calls `serde_json::from_slice`). There is no streaming `Deserializer` over an async reader in
// serde: decoding from a socket means framing into complete buffers first, with a different
// code path from `serde_json::from_reader` over a sync `Read`.
#[allow(dead_code)]
async fn count_events(api: Api<Memcached>) -> Result<usize, kube::Error> {
    let wp = kube::api::WatchParams::default();
    let stream = api.watch(&wp, "0").await?.boxed(); // COLOR: `.boxed()` to pin it
    // COLOR: `TryStreamExt::try_fold`, not `Iterator::fold`: a fallible async stream has its own
    // adapter family.
    stream.try_fold(0, |n, _ev| async move { Ok(n + 1) }).await
}

// ---------------------------------------------------------------------------------------------
// Test: a mock API server (tower-test), as in controller-rs's fixtures
// ---------------------------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use http::{Request, Response};
    use kube::client::Body;

    // COLOR: the test needs a runtime (`#[tokio::test]`) because `reconcile` is async; the
    // mock API server is a second task that must answer requests in the order they are made;
    // time is tokio's, controllable only with `start_paused = true` on a current-thread
    // runtime, and only for `tokio::time`, not for anything that reads the system clock.
    #[tokio::test(start_paused = true)]
    async fn new_memcached_gets_finalizer() {
        let (svc, mut handle) = tower_test::mock::pair::<Request<Body>, Response<Body>>();
        let client = Client::new(svc, "default");
        let ctx = Arc::new(Ctx {
            client: client.clone(),
            recorder: Recorder::new(client, Reporter::from("test")),
            image: "memcached:1.6.26-alpine".into(),
            request_timeout: Duration::from_secs(10),
        });
        let mut mc = Memcached::new("m1", MemcachedSpec { size: 3, container_port: 11211 });
        mc.metadata.namespace = Some("default".into());
        let server = tokio::spawn(async move {
            let (req, send) = handle.next_request().await.expect("service not called");
            assert_eq!(req.method(), http::Method::PATCH); // the finalizer JSON patch
            send.send_response(Response::builder().body(Body::from(b"{}".to_vec())).unwrap());
        });
        let _ = reconcile(Arc::new(mc), ctx).await;
        tokio::time::timeout(Duration::from_secs(1), server).await.unwrap().unwrap();
    }
}
