# The platform layer: capabilities, platforms and FFI — design

Status: a design. Nothing in it is built, and it proposes SPEC entries without writing them. The
probes in `docs/platform-examples/` were run on 2026-09-30 against wasmtime 49.0.1; they are
outside the gate. Every surface spelling below is provisional (marked `-- prov.` where it matters),
and every `A + E` result is provisional until errors are an effect (#18).

The question this answers: how does a checked program reach the world — files, sockets, clocks,
HTTPS — on WebAssembly now and on native code later, with one capability interface, an honest
trusted base, and no function colouring? The user's framing: "at some point we need to be able to
make a https request", and "WASI feels like cheating but importing libcurl is the same kind of
thing anyway". Both routes put someone else's TLS in the trusted base. What we control is our
capability interface and whether the boundary is listed.

Three layers, kept apart:

1. **Capabilities in the language** (§2). Designed from what the programs need (§3, the operator,
   the CLI tools), and from the language's own rules. No platform's shapes leak into it.
2. **Platforms** (§4). A platform is a package that implements the standard capability bundle.
   `wasi` implements it over WASI 0.2, and `posix` over libc. A program cannot tell which one it
   runs on.
3. **FFI to arbitrary C** (§7). Contracts in our existing modes, C resources as linear handles,
   callbacks, and a generated trusted base.

Contents:

- §0 Summary and recommendations
- §1 The constraints designed within
- §2 Layer 1: capabilities
- §3 The target programs
- §4 Layer 2: platforms and packages
- §5 The probes
- §6 The headline program: HTTPS with a bearer token and a custom CA, by two routes
- §7 Layer 3: FFI to C
- §8 The trusted base, route by route
- §9 Prior art
- §10 Staged plan
- §11 Open questions, with recommendations
- §12 What this document has not established

## 0. Summary and recommendations

**Architecture.**

- **One opaque type per host resource, one model each** (decision 31): `Conn`, `Listener`,
  `File`, `Dir`, `Clock`, `Http`, `Body`, and so on. Each is `VTy.opq k`, linear, never
  persistent. A handle created at run time is a one-word value (a descriptor or a host-table
  index). An operation takes it by `&mut` and hands it back. Buffers are lent to one call, as
  `slice 'a u8` or `slice mut 'a u8` (§2.4).
- **A bundle is an ordinary record of capabilities.** `main` declares the record it needs, and a
  function takes the sub-record it needs. There is no new type former (§2.8).
- **The platform interface is non-blocking operations plus one readiness wait**, the same on
  both platforms (§2.6). Blocking and event-loop execution are two handlers written in our
  language over that interface: `block_on` waits at once; a scheduler (#52) batches the waits.
  WASI 0.3's async is not used (the user's decision). On WASI the wait is 0.2's `poll`, used
  inside the `wasi` package and never exposed.
- **A platform is a package that provides a bundle.** The build selects one. The checker verifies
  that the package's bundle contains `main`'s, and an error names the missing capability.
  Platform-only extras come as a separately named extension bundle, so using one is visible
  (§4.1–§4.2).
- **The `wasi` package needs our own runner**, a small wasmtime embedder, `bcc-run`, for two
  things the wasmtime CLI cannot do: verify TLS against a cluster CA, and deliver SIGTERM to the
  program (§4.5, §5).

**HTTPS.** Both routes were checked (§6).

- **Route 1, `wasi:http` with the host doing TLS, works today, but not with the wasmtime CLI when
  the CA is private.** In wasmtime 49.0.1, `wasmtime run -S http` verifies servers against
  `webpki_roots::TLS_SERVER_ROOTS`, which is compiled in. No flag or environment variable
  changes that, and `wasi:http`'s `request-options` carries only timeouts. A Kubernetes API
  server's certificate is signed by the cluster CA, so the CLI cannot reach it: the probe got
  `ErrorCode::TlsProtocolError`. An embedder can override `WasiHttpHooks::send_request`. The
  probe's embedder (143 lines of Rust) verified against a private CA, sent the bearer
  token, and streamed a chunked watch body in three reads.
- **Route 2, a C TLS library over our own TCP capability, is feasible.** BearSSL 0.6 and zlib
  1.3.1 build unmodified with wasi-sdk 34 for `wasm32-wasip2`. A linked component ran a zlib
  round trip, and BearSSL produced a 222-byte ClientHello ready for our socket. BearSSL needed
  a seed injected first: without one, `br_ssl_client_reset` failed with `BR_ERR_NO_RANDOM`.
  Route 2 forces most of the FFI (§6.3).
- **Recommendation.** The first HTTPS request uses route 1 under `bcc-run` (stage P3). Route 2
  follows with the FFI (P4) and the native platform (P5), where it is the only route.

**FFI.** A `foreign` declaration states our type, the C prototype and a marshalling drawn from a
fixed vocabulary of our modes: an `imm` or `mut` view for the call's duration, owned in, owned
out, a scalar, a C string, an out-slot, a callback lent for the call. It declares no raw
pointers, and there is no unsafe block. Anything the vocabulary cannot express is written as a
C shim whose own contract it can express, and the shim is listed. The declaration is a row of
the generated trusted base (§7).

**In-process C and host-side WASI differ in exactly one respect** (§7.6). SPEC §11's contract is
the relation at the extern's type, and its frame part says that the rest of memory is left alone.

- A host-side implementation meets the frame part by construction. It reaches our memory only
  through the canonical ABI's copies, so a bug in the host's TLS can give wrong bytes but cannot
  break the memory model.
- An in-process C library must meet the frame part itself. Its memory safety becomes a
  hypothesis of every theorem about the program.

**The plan** (§10):

| stage | delivers |
|---|---|
| P1 | bundles, and `Args`, `Env`, the exit status, `Clock`, `Random` and `Fs`, on WASI components |
| P2 | `Net` and the readiness interface |
| **P3** | **`Http` and the first HTTPS request (route 1), plus `Signals`, under `bcc-run`** |
| P4 | FFI (zlib) |
| P5 | the native `posix` platform with route-2 TLS |

## 1. The constraints designed within

| constraint | source | what it forces here |
|---|---|---|
| An extern's contract is its semantic type; a checked `main` is safe under every implementation meeting its contracts | SPEC §11 *Externs* | platforms are interchangeable implementations of the same externs |
| No ambient authority; one capability per effect | decision 30; SPEC §11 *Capabilities* | every operation takes a capability or a handle derived from one |
| Host resources are opaque types with a model | decision 31 | one `VTy.opq k` per resource kind, no new former |
| I/O is a bundle of effects, ambient only in `main` (sugar), handler-implementable later | the user's decision; #18 | §2.8; the platform package is the outermost handler (§2.9) |
| Trust, not assurance ceremony: the checker reports, the user writes `trust e`, the trusted base is generated | the user's decision; #79, #126 | `extern`/`foreign` are not an unsafe escape; their rows are generated (§7.5) |
| No function colouring | the user's decision; decision 35; operator README §2 | the platform exposes non-blocking operations plus a wait; blocking is one handler (§2.6) |
| Portable lowerings | decision 25 | no semantics depends on a WASI-only feature; every capability maps onto both platforms (§4.4) |
| Threads eventually | the user's decision | no global mutable state in the platform layer; the wait state is a value (§2.7) |
| Heap allocation is explicit and an effect; no GC | the user's decisions; #54 | a C library allocates through our allocator (§7.4) |
| Errors will be an effect (#18) | the user's decision | `A + IoError` now, marked provisional |
| WASI's async is not used | the user's decision (this design) | §2.6 |
| Syntax is provisional; surface only one-way doors | the user's decision | spellings are marked; §11 lists the doors |

## 2. Layer 1: capabilities

### 2.1 Principles

1. **A resource kind is an opaque type with a model** (decision 31). A value of it can be moved
   and handed to an operation, never copied or inspected. Its model is a predicate: for a
   connection, the bytes still to be read and the bytes written so far. For a clock, the
   readings still to come. For a directory, the file tree below it.
2. **Handles are linear values of one word.** A connection is its descriptor or host-table
   index, not a cell. An operation takes the handle by move and hands it back first. At the
   surface that is `&mut conn`, the move-and-rebind row of typed elaboration §5.1, which costs
   no cell and no borrow. The standard streams stay cells (`ref input`, SPEC §11) until they are
   reworked (open question Q1).
3. **Authority is the handle.** Creating a handle needs a capability (`connect` needs `&mut Net`,
   `open` needs a `Dir`). Using a handle needs only the handle. Attenuation is creating a weaker
   handle: `open_dir` gives a subdirectory, and a connection is authority over one peer.
4. **Buffers are lent for the call** (§2.4). No operation keeps a view after it returns.
5. **Operations answer, they do not suspend** (§2.6). Whether a call waits by blocking or by
   yielding to a scheduler is a handler's choice. A platform package provides non-blocking
   primitives and a readiness wait.
6. **Every operation is an extern with a model implementation**, as `read_byte` is today. So the
   model meets each contract (a theorem, as `readByte_meets`), `bcc interp` runs the model, and
   a test can serve any capability with a handler.

### 2.2 The catalogue

`-- prov.` spellings. `slice 'a u8` is S3's `[Imm 'a U8]`, `slice mut 'a u8` is `[Mut 'a U8]`,
and `str 'a` is `slice 'a u8` with the UTF-8 invariant (strings design §2.2). Paths are
`slice 'a u8`, since OS strings are bytes (strings design P14). `IoError` is §2.5. Counts are
`i32` until a size type exists.

**Stdio** (exists: SPEC §11). `stdin : In`, `stdout : Out`, `stderr : Out`, plus S5's bulk
operations (branch `strings-s5`, not edited here). Every byte-stream handle in this design takes
their shape.

```
fn read_into(s: &mut In, buf: slice mut 'b u8) -> i32 + IoError     -- 0 at end of input
fn write_all(s: &mut Out, buf: slice 'b u8) -> 1 + IoError
```

**Args, Env.** Read-only, a snapshot taken at start. They are capabilities because they are
authority: the environment holds secrets.

```
fn arg_count(a: &Args) -> i32
fn arg(a: &Args, i: i32, into: &mut buf u8) -> 1 + IoError        -- appends argument i's bytes
fn env_get(e: &Env, name: slice 'b u8, into: &mut buf u8) -> 1 + IoError
fn env_iter(e: &Env) -> Iter<(slice 'e u8, slice 'e u8)>         -- views into the snapshot
```

**Exit status.** `main`'s result `i32` (SPEC §11 *Designed*). There is no `exit` operation. An
early exit is a return, so destructors run on the way out. Only the low 8 bits reach a POSIX
parent (see the Windows note in §4.4).

**Clock.**

```
type Instant = i64                                    -- monotonic nanoseconds; prov.
fn now(c: &Clock) -> Instant                          -- monotonic
fn wall(c: &Clock) -> i64                             -- nanoseconds since the Unix epoch
fn sleep_until(c: &mut Clock, t: Instant)             -- a wait with a deadline (§2.6)
```

`sleep_until` takes `&mut Clock` because a simulated clock (operator Part 3) advances on it.
Wall time is the same capability, since both are the same authority (timing).

**Random.** `fn fill(r: &mut Random, buf: slice mut 'b u8)`. It is cryptographic, and a platform
without a secure source does not provide it.

**Fs.** The capability is a set of directories named by the runner, never a global path space.

```
type Fs = { dirs: … }                                 -- named directory handles; prov. (§2.8)
fn open(d: &Dir, path: slice 'p u8, mode: Mode) -> File + IoError
fn open_dir(d: &Dir, path: slice 'p u8) -> Dir + IoError     -- attenuation: a subtree
fn read_into(f: &mut File, buf: slice mut 'b u8) -> i32 + IoError
fn write_all(f: &mut File, buf: slice 'b u8) -> 1 + IoError
fn seek(f: &mut File, pos: i64) -> 1 + IoError
fn stat(d: &Dir, path: slice 'p u8) -> Stat + IoError        -- kind, size, modification time
fn remove(d: &Dir, path: slice 'p u8) -> 1 + IoError
fn rename(d: &Dir, from: slice 'p u8, to: &Dir, to_path: slice 'q u8) -> 1 + IoError
fn entries(d: &Dir) -> Iter<Entry, 1 + IoError>
fn close(f: File) -> 1 + IoError                      -- also the destructor, error dropped (§2.3)
```

Paths are resolved *beneath* their directory: `..` past the directory and absolute paths are
errors. That is part of the contract, and every platform must implement it (§4.4). The
Kubernetes service-account directory is one named `Dir`, so a program handed only it can read
the token and the CA and nothing else.

**Net.** TCP, and name resolution inside `connect`.

```
fn connect(n: &mut Net, host: str 'h, port: i32) -> Conn + IoError      -- resolves, tries each address
fn resolve(n: &mut Net, host: str 'h) -> Iter<IpAddr, 1 + IoError>
fn listen(n: &mut Net, addr: IpAddr, port: i32) -> Listener + IoError
fn accept(l: &mut Listener) -> Conn + IoError
fn read_into(c: &mut Conn, buf: slice mut 'b u8) -> i32 + IoError        -- 0 when the peer closed
fn write_all(c: &mut Conn, buf: slice 'b u8) -> 1 + IoError
fn shutdown_write(c: &mut Conn) -> 1 + IoError
fn close(c: Conn) -> 1 + IoError
```

`Net` may be attenuated: `net_to(&mut Net, host, port) -> Dialer` is authority to reach one
endpoint (Eio's advice to pass `fun () -> Eio.Net.connect net addr`, §9). UDP is later: no
target program needs it.

**Tls.** A transformation of a connection, not a new authority. It needs randomness (the
handshake) and a clock (certificate validity), and the types say so. That is the BearSSL finding
of §5.4 made visible.

```
fn trust_pem(pem: slice 'p u8) -> TrustAnchors + TlsError          -- a value: the CA is data
fn tls_connect(c: Conn, server_name: str 'n, trust: &TrustAnchors,
               r: &mut Random, clk: &Clock) -> TlsConn + TlsError
-- TlsConn has Conn's read_into / write_all / close
```

A client certificate is later. In-cluster clients authenticate with a bearer token.

**Http.** The operator's effect (`docs/operator/operator.bc` §1.5), with its body a stream of
chunks:

```
effect Http { fn send(req: &Request) -> Response + HttpError }              -- operator.bc §1.5
data Response = { status: i32, headers: Headers, body: Body }
fn read_into(b: &mut Body, buf: slice mut 'b u8) -> i32 + HttpError          -- 0 at the end
fn chunks(b: Body) -> Iter<Bytes, 1 + HttpError>                             -- for `lines`, decoders
fn http_client(n: &mut Net, trust: &TrustAnchors, …) -> HttpClient           -- a handler of Http
```

`Body` is linear and its destructor closes the connection, on every exit (operator G3). Two
handlers implement `Http` behind the same signature: the library's HTTP/1.1 over `Net` and `Tls`,
and a host-backed one where the platform offers HTTP (`wasi:http`). The CA is always a value in
the program. How a host-backed handler honours it is §6.1.

**Signals.** Designed from the one need: shutdown. Kubernetes sends SIGTERM before killing a pod,
and the operator drains on it (`terminated(&mut signals)`, operator.bc §2.7).

```
fn shutdown(s: &mut Signals) -> Shutdown       -- a readiness source: fires once, on SIGTERM or SIGINT
fn requested(s: &Shutdown) -> bool
```

There is no general signal handling. Raw signals are a `posix` extension (§4.1).

### 2.3 Destructors for host resources (operator N6, SPEC §12 Open)

A host handle's destructor is an extern (`close`), so the handle is in SPEC §12's class 2 and an
unused one is closed at the end of its scope. **A failing close in a destructor drops the error.**
A caller who needs the error calls `close` explicitly, which returns it. A value whose silent
destruction is a bug uses the `linear` binder (SPEC §12 *Opt-out*), and the checker rejects any
path that forgets it. In the model, `close` is total and frees the model state. In `dtorE`, the
destructor is the extern's call, typed by the extern's contract, so `dtor_wf` needs the extern
context as an argument. That is the one kernel-side change, and it is small: `dtorE` is built
from existing rules.

### 2.4 Borrowing buffers across calls

Every data-moving operation takes a view lent for the call: `slice 'b u8` in, `slice mut 'b u8`
out, with the count returned. That is POSIX's `read(fd, p, n)` and `write(fd, p, n)`, and
S5's `read_into`/`write_all` (strings design §4.2). No operation keeps the view. So:

- a borrow ends when the call returns, and the checker already enforces it (the lifetime `'b`
  is the call's);
- one buffer can be reused across a loop of reads (`let mut buf = box buf[u8](16384)`, lent
  per call);
- a reading loop is an iterator over a lent buffer, per observation (decision 40).

A completion-based backend (io_uring, IOCP) keeps the buffer while the operation is in flight,
beyond one call. The same surface `read(&mut c, &mut buf)` then lowers by the move-and-rebind
row, with the buffer owned in and handed back, when the parameter type is owned. The surface does
not change, and the choice is per platform, by type (open question Q8). WASI 0.3's streams are
completion-based too, and are not used.

**Cost on WASI 0.2** (§4.5). `input-stream.read` returns a `list<u8>`, which the canonical ABI
allocates in our memory through our exported `realloc`. So a read into a lent view costs one
allocation and one copy, where POSIX `read(2)` fills the view in place. The package can make its
`realloc` return the lent view's address for that one call, which removes both. That is a
package-internal optimization, and it has not been tried (§12).

### 2.5 Errors (provisional, #18)

One small portable error type, designed from what programs do with errors:

```
data IoError = NotFound | PermissionDenied | AlreadyExists | ConnectionRefused | ConnectionReset
             | TimedOut | Unsupported | InvalidInput | Other(i32)           -- prov.; Other: the platform's code
data TlsError  = Handshake | Certificate | Protocol | Io(IoError)
data HttpError = Io(IoError) | Tls(TlsError) | Protocol | Status(i32)       -- operator.bc's, extended
```

Each package maps its native codes: `errno` for `posix`, `error-code` for `wasi`. Neither
platform's enumeration is copied. `WouldBlock` is absent: it exists only below the interface
(§2.6). When #18 lands, `A + IoError` becomes `A / {Fail<IoError>}`. The operations and the
packages do not change, only their result types.

### 2.6 Blocking and event loops: the platform interface

The user's rule is that the same operation must run blocking or on an event loop, chosen by the
handler, and that the event loop is ours. So a platform package exports two levels.

**The primitive level** (the platform interface), the same on both platforms:

```
-- inside a platform package; not the program's API
fn try_read(h: &mut H, buf: slice mut 'b u8) -> Ready(i32) | WouldBlock | Err(IoError)
fn try_write(h: &mut H, buf: slice 'b u8) -> Ready(i32) | WouldBlock | Err(IoError)
fn try_accept(l: &mut Listener) -> Ready(Conn) | WouldBlock | Err(IoError)
fn start_connect(n: &mut Net, addr: IpAddr, port: i32) -> Pending + IoError
fn finish_connect(p: &mut Pending) -> Ready(Conn) | WouldBlock | Err(IoError)
fn wait(w: &mut Waiter, interests: slice 'i Interest, deadline: Instant + 1) -> ReadySet
-- Interest = (borrowed handle, Readable | Writable); Shutdown is an Interest too
```

**The answering level** is library code in our language, with one copy per handler by
specialization (decision 35, operator README §2):

- **`block_on`**: `read_into` is `try_read`. On `WouldBlock` it calls `wait([h], none)` and
  retries, and `sleep_until(t)` is `wait([], t)`. That is a blocking call, with no state machine
  (operator README §6).
- **A scheduler** (#52): on `WouldBlock` a task yields `Wait(interest)`. The scheduler collects
  the interests of all waiting tasks and makes one `wait` with the earliest deadline.

A capability operation is written once (`read_into` in the library), and nothing in a caller
changes between the two.

**Mapping.**

| primitive | WASI 0.2 (inside `wasi`) | POSIX (inside `posix`) |
|---|---|---|
| `try_read` | `input-stream.read(n)`: non-blocking, an empty list is `WouldBlock` | `read(2)` on `O_NONBLOCK`; `EAGAIN` is `WouldBlock` |
| `try_write` | `check-write`, then `write` | `write(2)` on `O_NONBLOCK` |
| connect | `tcp-socket.start-connect` / `finish-connect` | `connect(2)` giving `EINPROGRESS`, then `getsockopt(SO_ERROR)` |
| `Interest` | the handle's `subscribe()` pollable, created once per handle and direction and dropped with the handle | `(fd, POLLIN/POLLOUT)` |
| `wait` | `wasi:io/poll.poll(list<borrow<pollable>>)`, with a `monotonic-clock.subscribe-instant` pollable for the deadline | `poll(2)`; `epoll_wait` or `kevent` as optimizations |
| `Shutdown` | a pollable from `bcc-run`'s import (§4.5); WASI has none | `signalfd` (Linux) or a self-pipe written by the handler (both POSIX) |

**Where WASI 0.2 forces blocking.**

- Every `wasi:filesystem` descriptor operation is a plain function with no pollable: `open-at`,
  `read`, `write` and `stat` block the instance until they return. POSIX is the same for
  regular files, which are always "ready". So file I/O blocks on both platforms. An asynchronous
  file operation needs a thread pool or io_uring, both later.
- `poll` itself blocks, which is the point. `wasi:io/poll` says "This function traps if either: - the
  list is empty, or: - the list contains more elements than can be indexed with a `u32` value." The package therefore never calls it with nothing to wait for.
- Nothing else in what we use blocks. DNS (`resolve-addresses`, then `resolve-next-address`
  with a pollable), TCP, streams, `wasi:http`'s response future and the clock are all pollable.
  POSIX is *worse* at DNS: `getaddrinfo` blocks, so a scheduler on `posix` resolves on a
  thread, or with its own resolver over UDP (later).

WASI 0.2's `blocking-read` and `blocking-write-and-flush` would block the whole instance, and
the package does not use them. Nor does it use WASI 0.3's `stream`/`future` or async lift/lower.

### 2.7 Threads (later), and what this leaves open for them

- The wait state is a value, `Waiter`, owned by whoever waits (`block_on` or a scheduler), not a
  global. Each thread has its own.
- Handles are linear, so moving a handle to another thread is a move. A future `Send`-like rule
  is a property of the opaque kind (a WASI resource is per-instance; a POSIX fd is per-process).
- The primitives take `&mut` of a handle, so two threads cannot use one handle without the
  borrow checker. A connection split into read and write halves (`split(c) -> (Reader, Writer)`,
  rejoined before `close`) is the way to share one.
- `Shutdown` delivery is per process. A threaded runtime gives it to one waiter, which tells the
  others. That is library code.
- WASI 0.2 has no threads (§4.3). Threads will therefore come to `posix` first, and a threaded
  program will be non-portable until WASI has them. That is the one asymmetry this design
  cannot remove.

### 2.8 Bundles

**A bundle is a record of capabilities.** The standard bundle, as a record type (`-- prov.`;
named fields are stage 8):

```
type Std = { stdin: In, stdout: Out, stderr: Out, args: Args, env: Env, clock: Clock,
             random: Random, fs: Fs, net: Net, http: Http, signals: Signals }
```

A program's own bundle is any sub-record, such as `{ fs: Fs, http: Http }`.

- **`main` declares its bundle**, `fn main(caps: { net: Net, stdout: Out }) -> i32`, or
  mentions capabilities by name under the ambient sugar, which infers the record (SPEC §11
  *Sugar*, generalized from the three stream names).
- **Least authority by passing less.** A function takes the capabilities it uses, each lent
  (`f(&mut caps.net, &caps.clock)`), or a sub-record moved and handed back.
- **Splitting** is record destructuring, a derived rule (SPEC §5 *Records*).

**What the existing machinery supports.**

| need | supported by | status |
|---|---|---|
| a record of capabilities as `main`'s residual | `main : F (Caps ⊗ A)`, `Caps` a right-nested tuple (SPEC §11) | today, for the three streams |
| destructuring a bundle, passing a component | records are `⊗` trees; destructuring is derived (§5) | today |
| lending several capabilities to one call, each at its own lifetime | typed elaboration §5.1: "A call may lend several places, each lowered separately, in argument order" | today |
| moving a sub-bundle to a callee that hands it back | the move-and-rebind row of §5.1 | today, as a tuple |
| lending a sub-bundle as **one record of borrows at one lifetime** (`{ fs: mut 'c Fs, net: mut 'c Net }`) | core: `withborF2` for two cells, nested for more (SPEC §5 *Family borrows*) | **gap (surface)**: typed elaboration §5.1 has no row that lends a record of cells as a record of borrows |
| the same through the block form | `withborS` | **gap (spec)**: its leaf class is "built from `1`, `0`, `⊗`, `⊕`, `Ref`, `!`, `X`, `μ`", which does not list `VTy.opq` (SPEC §5 says of the rest "not derived, not known to be blocked") |
| named fields (`caps.net`) | stage 8 `data` with named fields | planned (operator README §5.1) |
| a bundle inferred from the names `main` mentions | SPEC §11's ambient trigger | today for `stdin`/`stdout`/`stderr` only; the trigger becomes "names of the selected platform's bundle" |

The two gaps are precise. The first is one row of the lend table, elaboration only. The second
is a question for `withborS`'s side conditions. `VTy.opq` has `Δ ⊢ k ⊐ @a` at every `@a` (SPEC
§11), so it satisfies the outlives side condition that the list stands in for. Settling it is
one check of `withborS`'s proof, not a new rule. Nothing about bundles needs a type former or a
`CDerives` rule.

### 2.9 Bundles and handlers (#18)

When capabilities become effects handled by handlers, each capability's operations become an
`effect` signature, as the operator already writes `Http`. The platform package is then the
**outermost handler for the bundle**: `main` runs inside `with platform_handlers(std) { … }`.
A test replaces any component with its own handler. Nothing in this design changes at that point:

- a capability's operations are already externs, "not rules, so a capability can later be served
  by a user-defined handler" (SPEC §11 *Designed, not built*);
- a bundle is already a record of the values the handlers close over;
- a stateful handler lends its state, which is the "borrow presented through an interface" of
  `docs/ideas-handlers-and-borrows.md`.

## 3. The target programs

Each program gives its intended surface (`-- prov.` throughout), the capabilities it needs, and
what each platform must provide. "Library" means our code, checked, not trusted.

### 3.1 TCP echo server

```
fn main(caps: { net: Net, stderr: Out, signals: Signals }) -> i32 =
  let l = match listen(&mut caps.net, ip4(127, 0, 0, 1), 7000) {
    inl l -> l | inr e -> { report(&mut caps.stderr, e); return 1 } };
  let stop = shutdown(&mut caps.signals);
  let mut buf = box array[u8](4096);
  for conn in accepts(&mut l, &stop) {                -- div; ends when `stop` fires
    for chunk in reads(&mut conn, &mut buf) { write_all(&mut conn, chunk) }
  };                                                  -- each `conn` is closed by its destructor
  0
```

- **Capabilities:** `Net` (listen), a `Listener` and `Conn`s, `Signals`, `stderr`.
- **One connection at a time** under `block_on`. Concurrent connections need #52's scheduler,
  and the source is unchanged.
- **`wasi`:** `wasi:sockets/tcp` listen and accept, and a stream per connection. Runner flag
  `-S inherit-network` (§5.3). `Shutdown` needs `bcc-run`.
- **`posix`:** `socket`, `bind`, `listen`, `accept4(SOCK_NONBLOCK)`, `read`/`write`, and
  `signalfd` or a self-pipe.

### 3.2 File copy with errors

```
fn copy(src: &Dir, from: slice 'a u8, dst: &Dir, to: slice 'b u8, buf: slice mut 'c u8) -> i64 + IoError =
  let mut i = open(src, from, Read)?;           -- `?` stands for #18's propagation; prov.
  let mut o = open(dst, to, CreateTruncate)?;
  let mut n = 0;
  for k in reads(&mut i, buf) { write_all(&mut o, prefix(buf, k))?; n = n + k };
  close(o)?;                                    -- explicit: a failed flush on close is an error here
  n                                             -- `i` is closed by its destructor
```

- **Capabilities:** `Fs` (two `Dir`s, possibly one), `File`s.
- **`wasi`:** `wasi:filesystem` preopens (`--dir host::guest`), `open-at`, `read`/`write`, and
  `drop` for close.
- **`posix`:** `openat` beneath a directory descriptor (§4.4 for the confinement), then
  `read`, `write` and `close`.
- **Errors** are `NotFound`, `PermissionDenied` and `Other`. A partial copy leaves `to` behind,
  as `cp` does.

### 3.3 Env, args and the exit code

```
fn main(caps: { args: Args, env: Env, stdout: Out, stderr: Out }) -> i32 =
  if arg_count(&caps.args) < 2 { write_all(&mut caps.stderr, &"usage: greet NAME\n"); return 2 };
  let mut name = box buf[u8](64);
  arg(&caps.args, 1, &mut name);
  let mut greeting = box buf[u8](16);
  match env_get(&caps.env, &"GREETING", &mut greeting) { inl _ -> () | inr _ -> push_lit(&mut greeting, "hello") };
  write_all(&mut caps.stdout, &greeting); write_all(&mut caps.stdout, &" "); write_all(&mut caps.stdout, &name);
  0
```

- **`wasi`:** `wasi:cli/environment` (`get-arguments`, `get-environment`) is copied into our
  memory at start. The status goes out through `wasi:cli/exit` `exit-with-code` (`@since`
  0.2.12 in the WIT read). The runner needs `-S inherit-env` or `--env` for the environment.
- **`posix`:** `argv`/`environ` at start; `main` returns the status.

### 3.4 A timer

```
fn main(caps: { clock: Clock, stdout: Out }) -> i32 =
  let t0 = now(&caps.clock);
  sleep_until(&mut caps.clock, t0 + 100_000_000);
  write_all(&mut caps.stdout, &"100 ms later\n"); 0
```

- **`wasi`:** `monotonic-clock.now`, and `subscribe-instant` plus `poll` inside `wait`. This is
  exactly the `wat-component` probe (§5.1), which slept 100 ms on a pollable.
- **`posix`:** `clock_gettime(CLOCK_MONOTONIC)` and `poll` with a timeout (or `nanosleep` under
  `block_on`).
- A test's `simulated` clock handler (operator Part 3) advances virtual time instead. The source
  is unchanged.

### 3.5 The watch stream (Kubernetes long poll)

```
fn watch(h: &mut HttpClient, path: str 'p, token: slice 't u8) -> Iter<Event, 1 + WatchError> =
  gen {
    let resp = send(h, &get(path).bearer(token).query("watch", "1"))?;
    for line in lines(chunks(resp.body)) { yield decode::<Event>(&line)? }
  }

fn main(caps: { fs: Fs, env: Env, net: Net, http: Http, random: Random, clock: Clock,
                stdout: Out, signals: Signals }) -> i32 =
  let sa = open_dir(&caps.fs.root, &"/var/run/secrets/kubernetes.io/serviceaccount")?;
  let token = read_all(&sa, &"token")?;
  let trust = trust_pem(&read_all(&sa, &"ca.crt")?)?;
  let mut h = in_cluster(&mut caps.http, &caps.env, &trust)?;       -- KUBERNETES_SERVICE_HOST/PORT
  let stop = shutdown(&mut caps.signals);
  for ev in take_until(watch(&mut h, &"/api/v1/pods", &token), &stop) {
    write_all(&mut caps.stdout, &ev.name); write_all(&mut caps.stdout, &"\n")
  };
  0
```

- **Capabilities:** `Fs` (the service-account directory only), `Env`, `Http` (constructed from
  `Net` and `TrustAnchors` by the library, or taken from the host), `Signals`, `stdout`.
- **The watch body** is chunked HTTP/1.1, read as a stream of JSON lines under a `for`:
  generators (SPEC §15), `lines` (the adapter library), and `decode` (operator N8).
- **`wasi`, route 1:** the host's `wasi:http` does TCP, TLS and chunked decoding, and the body
  is an `input-stream`. That was run in the probe (§5.2) against a local stand-in, with three
  chunks arriving 200 ms apart and read in three reads.
- **`wasi`, route 2, and `posix`:** the library's HTTP/1.1 over `Conn` and `TlsConn`.

### 3.6 Calling zlib

```
foreign "z" version "1.3.1" {                                         -- prov.
  fn compress_bound(n: u64) -> u64 = c "compressBound"
  fn compress2(dst: slice mut 'd u8, src: slice 's u8, level: i32) -> (i32, u64)
    = c "compress2"(dst.ptr, out dst.len, src.ptr, src.len, level)   -- destLen is in/out
  type Inflater = c "z_stream *" new c "bc_inflate_new" drop c "bc_inflate_end"   -- a shim, §7.3
  fn inflate(z: &mut Inflater, src: slice 's u8, dst: slice mut 'd u8) -> (i32, i32, i32)
    = c "bc_inflate"(z, src.ptr, src.len, dst.ptr, dst.len, out consumed, out produced)
}

fn main(caps: { stdin: In, stdout: Out }) -> i32 =
  let mut z = Inflater::new()?;                 -- linear; its destructor calls inflateEnd
  let (mut i, mut o) = (box buf[u8](4096), box buf[u8](16384));
  for chunk in reads(&mut caps.stdin, &mut i) { … inflate(&mut z, chunk, &mut o) … write_all(&mut caps.stdout, …) };
  0
```

- **Capabilities:** none beyond the streams. zlib does no I/O, so its declaration needs none
  (§7.2).
- **Forces:** views lent for a call, out-slots, a foreign handle with a destructor, and a C shim
  (`z_stream` must not move: zlib's internal state points back to it, so the shim allocates it).
- **`wasi`:** zlib built with wasi-sdk and linked into our component. The probe (§5.4) linked a
  round trip.
- **`posix`:** the system `libz`, linked by clang.

### 3.7 The headline: HTTPS GET with a bearer token and a custom CA, streamed

§3.5 without the watch: `send`, then `for chunk in reads(&mut resp.body, &mut buf) { write_all(&mut
stdout, chunk) }`. §6 evaluates it by both routes.

## 4. Layer 2: platforms and packages

### 4.1 A platform is a package that provides a bundle

"Package" here means only what this needs, not a package manager (that is #63):

- **A package is a named, versioned library unit**: a directory of `.bc` modules (`include`-able,
  decision 38 *prelude and include*), plus a manifest.
- **The manifest** lists the bundle type the package provides, and for each extern it implements:
  the contract (our type), the implementation (a WASI import name, a C symbol and library, or
  our own code) and its assurance level. It also lists the runner features it requires.
- **The models** of its opaque kinds live in `Core/` with their `*_meets` theorems, as
  `Core/Stdio.lean` does for stdio. A package's models are shared by every platform that
  implements the same kinds. That is what makes platforms interchangeable: `wasi` and `posix`
  implement the same externs at the same types, against the same models.
- **Linking.**
  - The build takes `main`, the library and the selected package's modules as one whole program
    (monomorphization and 0-CFA need the whole program).
  - The package's externs become imports: WASI imports for `wasi`, C symbols for `posix`.
  - Its C libraries, if any, are linked alongside (§7.7).

Two platform packages, and their extensions:

| package | provides | extension bundle (named, opt-in) |
|---|---|---|
| `wasi` | `Std` over WASI 0.2 (+ `bcc-run` for `Shutdown` and TLS trust) | `wasi.Ext`: `HostHttp` (the host's HTTP handler without our TLS), later `wasi:keyvalue` or config |
| `posix` | `Std` over libc | `posix.Ext`: `UnixNet` (Unix-domain sockets), `Spawn` (processes), `Pipes`, `RawSignals`, `Perms` (chmod, chown) |

A program that names `posix.Ext` in its bundle does not build against `wasi`, and the build
error says why. So non-portability is visible in `main`'s signature.

### 4.2 Selecting the platform: compile time, and run time as the same mechanism

**Compile time (the default).** `bcc build --platform wasi` (`-- prov.`) selects the package.
The check is a type check: `main`'s bundle type must be a sub-record of the package's provided
bundle. On failure the checker names the field and the package:

    error: main needs `signals: Signals`, which platform `posix-minimal` does not provide

The elaborator builds the projection from the provided record to `main`'s. That is record
destructuring (§2.8), with no new rule.

**Run time (a multiplatform binary).** The same mechanism with the choice as a value. The entry
point receives what the running platform provides:

```
fn main(caps: { std: Std, ext: 1 + UnixNet }) -> i32 = …       -- feature detection is a capability query
```

- **The standard bundle has one type on every platform.** Its kinds are platform-independent
  (§4.1), so a program generic over the platform is not needed. There is one `Net`, and
  whichever implementation is linked serves it.
- **What varies at run time is which implementation serves an extern**, and what is optional is
  an extension, offered as `1 + E`.
- **The `1 + E` value** is filled by the package at start: whether io_uring is available,
  whether the runner offers `bcc-run`'s trust import, whether this is a POSIX system with
  Unix-domain sockets. The program branches with an ordinary `match`.

A "multiplatform binary" is within one binary format. No binary runs both as a WASI component
and natively, so the run-time choice is among variants of one family: Linux kernels with or
without io_uring, or a component under `bcc-run` or under the plain wasmtime CLI.

**Lowering: dispatch inside the package, not specialization of the program.** Two ways exist:

- **Specialization.** One copy of the whole program per platform variant, chosen at entry. It
  costs code size, and it buys nothing, because the program's own code does not differ between
  variants: they differ only below the extern boundary.
- **Dispatch.** Each extern implementation of a multi-variant package switches on a tag fixed
  at start: `br_table` in Wasm, `switch` in LLVM. There is no indirect call, so decision 25 is
  kept (today's backend emits no `call_indirect`).

**Recommendation.** Dispatch inside the package. Compile-time selection is the case where the
tag is a constant and the switch folds away, so single-platform builds cost nothing, and the two
are one mechanism. Specialization happens only where it already happens in whole-program
compilation. If a handler's computation type differs between variants (a blocking `Net` in one,
a suspending one in another), every caller is copied by decision 35's specialization. That is a
compile-time handler choice, not a platform choice.

### 4.3 Coverage: WASI against what an operator or a CLI needs from Linux

What was read:

- the WIT of **WASI 0.2.12** and **0.3.0** as shipped in wasmtime 49.0.1's source
  (`crates/wasi/src/p2/wit`, `crates/wasi/src/p3/wit`, `crates/wasi-http`, `crates/wasi-tls`),
  on 2026-09-30;
- the WASI repository's `README.md` ("WASI 0.3 (Preview 3) is the current preview") and
  `docs/Proposals.md`, fetched the same day;
- its release list: v0.3.1 was published 2026-08-11 and v0.3.0 on 2026-06-11. I read the 0.3.0
  WIT, not 0.3.1's.

"Present" means a stable interface in the WIT read. "Proposal" means a WASI proposal, or
`@unstable` in the WIT. "Absent" means neither.

| need | Linux | WASI 0.2.12 | WASI 0.3.0 | `wasi` package provides it via | `posix` provides it via |
|---|---|---|---|---|---|
| files | `openat`, `read`, `write`, `fstat`, `renameat`, `unlinkat`, `getdents64` | present: `wasi:filesystem` (preopens only) | present | host | syscalls |
| TCP, UDP | `socket`, `connect`, `bind`, `listen`, `accept4` | present: `wasi:sockets` `tcp`, `udp` | present | host (`-S inherit-network`) | syscalls |
| DNS | `getaddrinfo` (libc; blocking) | present: `ip-name-lookup` (pollable) | present | host (`-S allow-ip-name-lookup`) | libc, on a thread under a scheduler |
| clocks | `clock_gettime` | present: `monotonic-clock`, `wall-clock`; timezone `@unstable(feature = clocks-timezone)` | present (`system-clock`) | host | syscalls |
| random | `getrandom` | present: `wasi:random` | present | host | syscall |
| args, env | `argv`, `environ` | present: `wasi:cli/environment` | present | host | libc start-up |
| stdio | fds 0–2 | present: `wasi:cli/stdin`, `stdout`, `stderr` | present | host | fds |
| exit status | `exit_group` | present: `exit(result)`; `exit-with-code(u8)` `@since(version = 0.2.12)` | present | host | return from `main` |
| HTTP client | none (a library) | present: `wasi:http/outgoing-handler`, host TLS with compiled-in roots | present | host; custom CA only under `bcc-run` (§6.1) | library over `Net` + `Tls` |
| HTTP server | none (a library) | present: `incoming-handler` (host owns the listener) | present | not used: the echo server and `/metrics` use `Net` | library |
| readiness polling | `poll`, `epoll_wait`, `kevent` | present: `wasi:io/poll` | replaced by component-model `async` | host (0.2 only; 0.3's async not used) | syscalls |
| processes (spawn, wait) | `clone`/`fork`, `execve`, `waitid` | **absent** | absent | not provided | `posix.Ext` `Spawn` |
| signals (SIGTERM) | `rt_sigaction`, `signalfd` | **absent** | absent | `bcc-run` import (§4.5); the wasmtime CLI cannot | `signalfd` or a self-pipe |
| threads | `clone`, `futex` | **proposal**: wasi-threads (Phase 1); wasmtime `-S threads`: "Enable support for WASI threading imports (experimental). Implies preview2=false." | proposal: component-model threading (🧵, wasmtime `-W component-model-threading`) | not yet | pthreads (later) |
| mmap | `mmap` | **absent** | absent | not provided | `posix.Ext` if a program needs it |
| Unix-domain sockets | `socket(AF_UNIX)` | **absent**: `ip-address-family` is `ipv4`, `ipv6` | absent | not provided | `posix.Ext` `UnixNet` |
| pipes | `pipe2` | **absent**: stdio streams only | absent | not provided | `posix.Ext` `Pipes` |
| permissions, ownership | `fchmodat`, `fchownat`, `umask` | **absent**: `descriptor-stat` has type, link count, size and times, no mode or owner | absent | not provided | `posix.Ext` `Perms` |
| TLS | none (a library) | **proposal**: wasi-tls (Phase 1); `@unstable(feature = tls)`, wasmtime `-S tls` "experimental" | proposal | route 1 via `wasi:http`; route 2 via FFI | FFI (BearSSL or mbedTLS) |

For the operator (operator README §6 steps 6–8): everything it needs is present in WASI 0.2
except **SIGTERM**, which the runner must supply, and a **custom CA for HTTPS**, which either the
runner supplies (route 1) or our own TLS provides (route 2). Graceful shutdown on SIGTERM is a
requirement: Kubernetes sends it before killing a pod, and the operator drains on it (operator.bc
§2.7). Under the plain wasmtime CLI, which installs no SIGTERM handler, the process dies at the
signal and the program sees nothing (I found no SIGTERM handling in `src/commands/run.rs` at
v49.0.1).

### 4.4 Each capability on each platform

The test the user set: a capability that maps naturally to one platform and awkwardly to the
other is a smell. Windows is noted where it differs materially.

| capability | `wasi` (WASI 0.2) | `posix` | fit | Windows |
|---|---|---|---|---|
| `Stdio` | `get-stdin`/`get-stdout`/`get-stderr` streams | fds 0–2 | both natural | handles; console is UTF-16 at the API |
| `Args`, `Env` | `get-arguments`, `get-environment`, copied at start | `argv`, `environ` | both natural | UTF-16; the package converts to bytes (WTF-8) |
| exit status | `exit-with-code(u8)` | return from `main` | both natural; 8 bits on both | 32-bit codes: the `i32` passes whole |
| `Clock` | `monotonic-clock`, `wall-clock` | `clock_gettime` | both natural | `QueryPerformanceCounter` |
| `Random` | `get-random-bytes` | `getrandom`/`getentropy` | both natural | `BCryptGenRandom` |
| `Fs` | preopened `descriptor`s; `open-at` resolves beneath by construction | `openat` does **not** confine `..` or symlinks. Linux ≥ 5.6 has `openat2(RESOLVE_BENEATH)`; elsewhere the package resolves component by component | **smell, toward POSIX**: confinement is native to WASI and must be built on POSIX | no `openat`; userspace resolution |
| `Net` | `tcp-socket` two-phase connect, streams, `ip-name-lookup` | sockets; `getaddrinfo` blocks | natural, except DNS on POSIX under a scheduler (**smell, toward WASI**, mild) | Winsock; IOCP is completion-based (Q8) |
| `Tls` | route 1: none needed; route 2: C library in-process | C library in-process | **smell, toward POSIX being harder**: WASI offers HTTPS with no TLS in our memory, POSIX never does | SChannel or a C library |
| `Http` | `wasi:http`, TLS in the host, roots compiled in | library over `Net` + `Tls` | **the largest smell**: native on WASI, a library on POSIX. The resolution is that `Http` is an effect with two handlers (§2.2), and the CA is program data that the host route must honour (§6.1) | library |
| `Signals` (`Shutdown`) | absent; `bcc-run` provides it | `signalfd`/self-pipe | **smell, toward WASI**: absent from the standard | `SetConsoleCtrlHandler`; services use SCM stop requests |
| the readiness `wait` | `poll(list<borrow<pollable>>)` | `poll`/`epoll`/`kqueue` | both natural (readiness on both) | IOCP is completion-based: Windows would need the owned-buffer lowering (Q8) or `WSAPoll` for sockets |

No capability is shaped after either platform. `Http` is the one whose natural home differs,
and the design absorbs it by making it an effect, not a primitive.

### 4.5 The `wasi` package: linking, the runner, versions and flags

**How our Wasm output links to WASI 0.2.** Established by the `wat-component` probe (§5.1):

1. **Imports.** The backend imports each WASI function by its canonical-ABI core signature, with
   module `"wasi:cli/stdout@0.2.12"` and name `"get-stdout"`, or
   `"[method]output-stream.blocking-write-and-flush"`, `"[resource-drop]output-stream"`, and so
   on. That is the same WAT subset we emit today: imports, one memory, no table.
2. **Exports.** `wasi:cli/run@0.2.12#run` as the entry, `memory`, and a `cabi_realloc` backed by
   our allocator. The canonical ABI "will use `realloc` both to allocate … and reallocate" when a
   result is a list or a string (component-model Explainer). So the host allocates in our memory
   through our allocator, and the allocator's specification must cover calls from the host.
3. **Wrapping.** `wasm-tools component embed <wit> --world <world>` then `wasm-tools component
   new`. The WIT world is generated from the externs the program actually uses. The component's
   import list is then the program's authority, and `bcc trusted` prints it.
4. **Today's `wasi_snapshot_preview1` imports** (`fd_read`/`fd_write`, `Backend/Wasm/Runtime.lean`)
   move to `wasi:cli/stdin`/`stdout` streams at P1. The plain LLVM counterpart does not change
   (`read(2)`/`write(2)`).

A detail found on the way: `borrow` is a WIT keyword, so the generated package is named `bcore`.

**Versions and flags** (all verified by the probes, wasmtime 49.0.1):

| need | `wasmtime run` flag |
|---|---|
| our backend's tail calls | `-W tail-call=y` (as `bcc run` passes today) |
| `wasi:http` | `-S http` (without it, instantiation fails: "resource implementation is missing") |
| TCP | `-S inherit-network` (without it: "Permission denied") |
| DNS | `-S allow-ip-name-lookup` (without it: "failed to lookup address information") |
| files | `--dir host::guest`, per preopened directory |
| environment | `-S inherit-env` or `--env NAME=VALUE` |

**Why a runner of our own (`bcc-run`).** Two requirements of the operator cannot be met by the
wasmtime CLI:

1. **A custom CA for HTTPS** (§6.1).
2. **Delivering SIGTERM** (§4.3).

`bcc-run` is a wasmtime embedder: `wasmtime`, `wasmtime-wasi` and `wasmtime-wasi-http` at a
pinned version, as in `custom-ca/host` (§5.2). Its `send_request` hook uses a rustls
`ClientConfig` whose roots are the trust anchors the program supplied. It also adds one small
interface of our own, `bcore:runner` (`-- prov.`):

```
interface runner {
  resource shutdown { subscribe: func() -> pollable; }    // fires on SIGTERM/SIGINT
  get-shutdown: func() -> shutdown;
  set-http-trust: func(pem: list<u8>) -> result;          // trust anchors for wasi:http's TLS
}
```

A component that imports `bcore:runner` does not run under the plain CLI. So the `wasi` package
imports it only when the program's bundle contains `Signals`, or an `Http` with custom trust.
The CLI remains enough for everything else. Features a runner may lack are offered as `1 + E`
(§4.2), not as optional imports: the component model instantiates only when every import is
satisfied. In the Explainer I read, I found no optional-import mechanism (§12).

**`bcc-run` in the trusted base.** It is host code, outside our memory. Its rows are wasmtime's
version, the hook (about 55 of the probe's lines, plus a dozen that load the CA) and rustls
with its crypto provider (§8).

### 4.6 The `posix` package

- **Needs the LLVM backend** (#21). It emits objects linked by clang against libc (glibc or
  musl on Linux, libSystem on macOS).
- **Each extern** is a small C-ABI function over one or two libc calls, written in C or in our
  own code once `foreign` exists (§7).
- **The readiness `wait`** is `poll(2)` first. `epoll` (Linux) and `kqueue` (BSD, macOS) are
  optimizations behind the same primitive.
- **`Shutdown`**: `signalfd` on Linux, a self-pipe written from a handler elsewhere. Both
  surface as one `Interest`.
- **Directory confinement**: `openat2(RESOLVE_BENEATH)` where the kernel has it, userspace
  resolution elsewhere.
- **Its trusted base** is libc, the kernel, the extern shims and the C libraries it links (§8).

## 5. The probes

`docs/platform-examples/run.sh` runs probes 5.1–5.3 and the TCP probe end to end, and
`c-libs/build.sh` runs 5.4. They need Rust with the `wasm32-wasip2` target, `wasm-tools`,
`openssl` and `python3`, and wasi-sdk for 5.4. They are outside the gate. Output on 2026-09-30,
wasmtime 49.0.1, wasm-tools 1.259.0, rustc 1.97.1, wasi-sdk 34:

### 5.1 A core module of our shape, as a WASI 0.2 component (`wat-component/`)

A hand-written core module in exactly the subset our backend emits: imports by canonical-ABI
signature, one memory, no table. It writes a line, sleeps 100 ms on a
`monotonic-clock.subscribe-duration` pollable, and writes another. `wasm-tools component embed` +
`component new` wrap it. `wasmtime run` printed both lines, 0.117 s wall time. This settles how
our output links (§4.5).

### 5.2 `wasi:http`: public roots under the CLI, a private CA under an embedder (`https-guest/`, `custom-ca/`)

`https-guest` is a Rust `wasm32-wasip2` component. It issues a GET through
`wasi:http/outgoing-handler` with an optional bearer token read from a preopened file, and streams
the body in 4096-byte reads. `custom-ca/` makes a private CA and a `localhost` certificate signed by
it (`make-ca.sh`), and serves a bearer-checked, chunked body of three JSON lines, 200 ms apart
(`server.py`), as a stand-in for the API server.

| run | result |
|---|---|
| `wasmtime run -S http` → `https://example.com/` | `status 200`, 713 bytes |
| `wasmtime run -S http` → the private-CA server | `request failed: ErrorCode::TlsProtocolError` |
| the same with `SSL_CERT_FILE=ca.crt` | the same error (the roots are compiled in) |
| `ca-host ca.crt` (embedder) → the private-CA server, with the token | `status 200`, three JSON lines, "body 159 bytes in 3 reads" |
| `ca-host` without the token | `status 401` |
| `ca-host` with a different CA | `request failed: ErrorCode::TlsProtocolError` |

### 5.3 TCP and DNS permissions (`tcp-guest/`)

A Rust component connects with `std::net::TcpStream` (which on `wasm32-wasip2` goes through the
same socket implementation as Unix, `library/std/src/sys/net/connection/mod.rs`). With no flags:
"Permission denied". With `-S inherit-network`, it connected to an IP. A host name then failed
("failed to lookup address information") until `-S allow-ip-name-lookup` was added.

### 5.4 C libraries built with wasi-sdk and linked into a component (`c-libs/`)

zlib 1.3.1 (10 files) and BearSSL 0.6 (all 277 files of `src/`) compiled with wasi-sdk 34's
`clang --target=wasm32-wasip2 -O2`, with no source changes and no failures. `probe.c` linked
against both is a component that ran under `wasmtime run`:

    zlib 1.3.1: 106 -> 63 -> 106 bytes, round trip ok
    bearssl: reset without a seed 0, error 8 (BR_ERR_NO_RANDOM = 8)
    bearssl: reset 1, state SENDREC, ClientHello record of 222 bytes ready for our socket

Two findings bear on the FFI:

- **A C library can need authority of its own.** BearSSL 0.6 has no entropy source for this
  target. The probe seeds it from `getentropy`, which wasi-libc serves from `wasi:random`.
- **On WASI that authority is visible.** The component's imports include `wasi:random/random`,
  `wasi:clocks/*` and `wasi:cli/*` because the C code linked them in. Natively the same calls are
  invisible. §7.2 makes them part of the declaration.

## 6. The headline program, by two routes

The program is §3.5/§3.7: read the service-account token and the cluster CA from a directory,
GET `https://$KUBERNETES_SERVICE_HOST/api/…` with `Authorization: Bearer <token>`, verify the
server against the CA, and stream the body through a reused buffer.

### 6.1 Route 1: `wasi:http`, with the host doing TLS

**The custom-CA check** (the question asked):

- **What `wasi:http` exposes to the guest.** `wasi:http` 0.2.12's `request-options` has
  `connect-timeout`, `first-byte-timeout` and `between-bytes-timeout`, and nothing else: no
  trust anchors, no client certificate, no TLS setting of any kind.
- **What the wasmtime CLI does.** In wasmtime 49.0.1,
  `crates/wasi-http/src/default_send_request.rs` builds its TLS configuration as

  ```rust
  let root_cert_store = rustls::RootCertStore {
      roots: webpki_roots::TLS_SERVER_ROOTS.into(),
  };
  let config = rustls::ClientConfig::builder()
      .with_root_certificates(root_cert_store)
      .with_no_client_auth();
  ```

  so the roots are compiled in. The CLI's hooks (`src/common.rs`, `HttpHooks`) override only
  `p2_outgoing_body_buffer_chunks` and `p2_outgoing_body_chunk_size`. The CLI's `-S` options
  include nothing for TLS roots, and `SSL_CERT_FILE` has no effect (§5.2).
- **So a private CA is impossible under `wasmtime run`**, and a cluster's API server uses one.
- **How an embedder does it.** `WasiHttpHooks` has "`send_request` … Send an outgoing request.
  This function will be used by the `wasi:http/handler#handle` implementation." The probe's
  `ca-host` implements it with its own rustls configuration and handles the request end to end
  (§5.2).
- **`wasi:tls` has the same limit.** It is the experimental guest-driven alternative
  (`-S tls`), and its default `RustlsProvider` is built from `webpki_roots::TLS_SERVER_ROOTS`
  (`crates/wasi-tls/src/providers/rustls.rs`). Its WIT's `client-handshake` constructor takes
  only `server-name` and the two streams. Custom roots again need an embedder, through
  `WasiTlsCtxBuilder::provider`.

**How our interface meets it.** The program's CA is a value (`trust_pem(bytes)`). The `wasi`
package's host-backed `Http` handler passes it to `bcc-run` through `bcore:runner`'s
`set-http-trust` when the client is made. Under the plain CLI, that import is absent: the program
gets `inr` for the host-trust capability (§4.2) and uses route 2, or fails at construction with a
named error. It never silently uses public roots.

**What route 1 needs from us:** the `Http`/`Body` externs over `wasi:http` types and streams
(package code), `bcore:runner`, and `bcc-run`. No FFI, no TLS code, and no HTTP code in our
language.

**Limits.** The CLI's `default_send_request` makes one HTTP/1.1 connection per request ("TODO:
we should plumb the builder through the http context"), and `bcc-run`'s hook as probed does too.
Connection reuse is a `bcc-run` matter. The response body's between-bytes timeout defaults to
600 s in `default_send_request`. A watch that is idle longer is cut, so `bcc-run` should set it
per request, or the program should pass `between-bytes-timeout` (the option exists).

### 6.2 Route 2: our HTTP over our `Net`, with a C TLS library

The stack, bottom up:

1. **`Conn`** from `connect(&mut net, host, 443)`: `wasi:sockets` or POSIX sockets.
2. **`tls_connect(conn, name, &trust, &mut random, &clock)`**, a library function over the
   foreign BearSSL engine. BearSSL does no I/O. It hands out records to send (`sendrec`) and
   takes records received (`recvrec`), and the library pumps them through `Conn`'s
   `read_into`/`write_all`. It is the natural fit for a readiness-based, non-blocking interface
   (§2.6): a `WouldBlock` on the socket is a yield, never a blocked C call.
3. **The trust anchors.** BearSSL takes them as C structures (`br_x509_trust_anchor`). Turning
   PEM into them is BearSSL's own decoder, called through a shim.
4. **HTTP/1.1 with chunked decoding** in our language (operator §1.5's `http_client`), checked
   and not trusted.

**The FFI features route 2 forces** (§7):

| feature | why |
|---|---|
| views lent for a call, in and out (`slice 'a u8`, `slice mut 'a u8`) | record buffers in and out of the engine |
| a foreign handle with a stable address and a destructor | `br_ssl_client_context` and its I/O buffer are large structures that must not move between calls |
| out-slots | `br_ssl_engine_sendrec_buf(&eng, &len)` returns a pointer and a length |
| a pointer *into* a foreign handle's own buffer, lent back to us for one call | `sendrec_buf` returns a view of the engine's buffer. Our contract: an `imm` view valid until the next engine call. The shim copies it out, or the declaration lends it at a lifetime scoped by the handle's `&mut` |
| authority passed in, not taken | entropy (`br_ssl_engine_inject_entropy`) from `Random`; the time for certificate validation from `Clock` |
| linking C objects into our module | our backend's output and wasi-sdk's objects in one component (§7.7) |
| one allocator | BearSSL allocates nothing itself, but zlib and most libraries call `malloc` |
| C shims | PEM → trust anchors; X.509 validation time from our clock rather than `time()` |
| **not** callbacks | BearSSL's engine API needs none. Callbacks are forced by other libraries (§7.3) |

**Natively**, the same stack with the system's sockets and a native BearSSL build. mbedTLS
(which uses `bio` callbacks) would force callbacks; BearSSL does not, which is a reason to
prefer it. Route 2 is the only route natively, and on WASI it removes `bcc-run`'s TLS row at the
price of putting TLS in our memory (§7.6).

### 6.3 Comparison

| | route 1 (`wasi:http`, host TLS) | route 2 (BearSSL over our `Net`) |
|---|---|---|
| runs today | yes, under an embedder (probed end to end) | parts probed; needs P2 and P4 |
| custom CA | through `bcc-run` only | a value passed to BearSSL, on every runner |
| TLS in our memory | no | yes (the frame hypothesis of §7.6) |
| HTTP in the trusted base | yes (hyper, in the host) | no (our checked code) |
| native counterpart | none: HTTP must be a library natively | the same code |
| language work | `Http` externs, `bcore:runner` | FFI (P4) |

## 7. Layer 3: FFI to C

### 7.1 The boundary is still an extern

A `foreign` declaration *is* an extern in SPEC §11's sense. Its contract is the semantic type
written on the left, and the right side says how the C function implements it. Nothing new
enters the kernel: no rule, no machine step, no unsafe block. The FFI is **not a general unsafe
escape hatch**, for three reasons:

- **The types on the left are our ordinary types.** There is no raw pointer type. A C pointer is
  never a value in our program, only a marshalling of one of our modes.
- **The marshalling vocabulary is fixed** (§7.2). A C function whose behaviour cannot be stated
  in it cannot be declared. It gets a C shim whose behaviour can, and the shim is part of the
  declaration, listed and hashed.
- **`trust e` stays separate.** It is for our own code the checker cannot type (#79). A `foreign`
  row is a claim about C code, and the generated trusted base lists it as one.

No Lean appears in the syntax. The contract is our type, and whether it is proved, tested or
assumed is recorded out of band (the trust report of #126).

### 7.2 Contracts in our modes

| our side (in the declaration's type) | C side | contract |
|---|---|---|
| `i32`, `i64`, `u8`, `bool` | `int32_t`, `int64_t`, `uint8_t`, `int` | by value |
| `slice 'a T` (argument) | `const T *p, size_t n` | readable for the call's duration only; not retained |
| `slice mut 'a T` (argument) | `T *p, size_t n` | readable and writable for the call only; C writes within `[p, p+n)` only |
| `&x : imm 'a T` / `&mut x : mut 'a T`, `T` flat | `const T *` / `T *` | one object, for the call only |
| `out T` | `T *` to a slot the wrapper provides | C writes it; we read it after the call |
| an owned foreign handle `H`, in | `H *` | consumed: C takes ownership; our value is gone |
| an owned foreign handle `H`, out | `H *` (null is an error) | a new linear value whose destructor is the declared `drop` |
| `&mut h : H` (handle lent) | `H *` | C may use and mutate the object for the call; the address is stable (the handle is never moved by us) |
| `cstr` from `slice 'a u8` | `const char *` | a NUL-terminated copy for the call (`with_cstr`, strings design P15), or in place with `terminate` |
| a callback `imm 'a !(A => B)` | `(fnptr, void *ctx)` | callable during the call only (§7.3) |
| `needs R` on the declaration | none | the C code uses the authority `R` (for example `Random`, `Clock`, `Fs`); callers must hold it |

Every row is a borrow for the call, owned in, or owned out: the three modes the user named. A
foreign function's type is then an ordinary `!(all 'a … . P => Q)`. Its contract is SPEC §11's
`vC true A ls δ v ρ`, and the Fundamental Property quantifies over its implementations as for any
extern.

**`needs`.** A C library's own calls to `getentropy`, `time()` or `open()` are authority that
our types would otherwise not see (§5.4). The declaration lists them, and a caller must pass the
capability. On WASI the claim is checked: the component's imports must be covered by the
program's declared authority, and `bcc` compares them at link time. Natively it is trusted, and
listed.

### 7.3 C resources and callbacks

**Handles.** `type Inflater = c "z_stream *" new c "…" drop c "inflateEnd"` declares an opaque
kind (`VTy.opq`) whose model is "a live object of that C type". It is linear. Its destructor is
the declared `drop`, an extern, so class 2 of SPEC §12 applies with §2.3's rule. The C object
lives in memory allocated through our allocator (§7.4) and never moves, so a library that keeps
back-pointers (zlib's `state->strm`) is safe. A struct the C API wants caller-allocated is
allocated by a shim, or by the wrapper as a block that is never moved.

**Callbacks** (C calling our code), by kind:

- **Lent for the call** (`qsort`'s comparator, `sqlite3_exec`'s row function, a `bio` read
  function called during one TLS call). Our side is a closure `imm 'a !(A => B)`, or any closure
  borrowed for the call. The backend emits one **trampoline** per callback type: a C-ABI function
  `(void *ctx, args…) → result` that calls the defunctionalized closure named by `ctx`. The
  closure's environment is lent for the call, so `ctx` points to a live cell.
  - In Wasm, C calls the trampoline through `call_indirect`, so the trampoline needs a function
    table entry. That is C's indirect call, not ours: our code still emits none (decision 25).
    Natively it is a function pointer.
- **Stored by C beyond the call** (a registration API). Forced only by libraries with event
  registration, and none of our target programs. Designed as an owned `Registration` handle
  holding the closure (a `box`), whose destructor unregisters. It is not in the first FFI stage.

Three rules for callbacks:

- **No suspension inside a callback.** C's stack is not a state machine, so a callback cannot
  yield to our scheduler. It is specialized at a non-suspending computation type (decision 35's
  mechanism): total or div, not `Async`. This is the one place where a colour is real, because C
  cannot be suspended, and the checker reports it there.
- **No unwinding through C.** A callback that fails must handle its failure and return a C status.
  When #18 lands, `Fail` is handled at the trampoline.
- **Re-entrancy is borrow-checked.** A callback can use only what its closure captured, which is
  disjoint from what the enclosing call lent to C.

### 7.4 Memory: one allocator

A C library linked into our module calls `malloc`, and our runtime has its own allocator
(`Backend/README.md`). Two allocators growing one linear memory must at least never hand out
overlapping blocks. **We provide `malloc`, `free`, `calloc` and `realloc` from our allocator**, as
Roc's hosts provide `malloc` and `free` to the application (§9), so disjointness is the
allocator's specification, not an agreement between two allocators. C's allocations are ambient
with respect to our allocation effect. A declaration that allocates says so (`allocates`), so
the effect views (#126) can report it.

### 7.5 How a foreign declaration becomes part of the generated trusted base

`bcc trusted <file>` today lists externs with their contract, implementation and level (SPEC §11
*Assurance*). A `foreign` row adds:

- the library name, version and a content hash of the linked object;
- the C prototype;
- the marshalling row used for each parameter;
- the shim's source hash, if there is one;
- the declared `needs`, and on WASI the imports actually present.

The rows are generated from the program: only the foreign functions reachable from `main` are
listed. The platform package's externs appear too, grouped under the package name and version.
`bcc report --against main` (#126) shows added or changed rows.

### 7.6 In-process C against host-side WASI, precisely (SPEC §11)

An extern's contract is `vC true A ls δ v ρ`: the implementation `v`, run at resource `ρ`, is in
the relation at `A`. The relation's `wpTSD` includes a frame: memory outside `ρ` is unchanged at
the end of every value run (the frame theorem `wpTSD_frame_own` is its consequence at
capabilities). So an implementation must do two things:

- **(a)** return a value in the relation at the result type;
- **(b)** leave the frame alone: no write outside what it was lent or owns, no read of freed
  memory, and no pointer kept past the call into memory it was only lent.

**A host-side implementation (WASI).**

- **(b) holds by construction, given the canonical ABI's correctness.** Host code has no
  pointer into our memory. It can reach our memory only through the canonical ABI: it reads
  argument lists at call time, and writes results into memory obtained from our `realloc` or
  into the return area we pass. It cannot keep anything past the call (Explainer: a `borrow`
  handle "must be dropped before the current export call returns").
- **(a) holds automatically at most of our types.** At `Bytes`, `i32 + IoError` or `Response`,
  every value the host can produce is in the relation. So a bug in the host's TLS or HTTP code
  can produce wrong bytes, but not a memory-model violation.
- **What is trusted for safety** is wasmtime's canonical ABI and its sandbox. **What is trusted
  for correctness** (the right server, the right bytes) is the host's TLS and HTTP.

**An in-process C library.**

- **(b) is a hypothesis on the C code**: its memory safety, its keeping to lent ranges, its not
  retaining lent pointers, its allocation through our allocator. A buffer overflow in a C
  certificate parser writes into our cells, and every theorem about the program is then void.
- **Wasm bounds the damage** to our linear memory (still our whole heap). Natively it is the
  whole process.
- **(a)** is as before.
- **What is trusted for safety** is the C library itself.

That is the single respect in which the two differ, and it is why route 2 has a stronger trust
assumption than route 1 even though both trust someone else's TLS for correctness. The trusted
base marks the difference: a `foreign` row carries `in-process`; a host import carries `host`.

### 7.7 Compiling it

- **Wasm.** Our backend emits WAT today, which a linker cannot combine with C objects. **The
  backend should emit a relocatable Wasm object**, with the `linking` and `reloc.*` custom
  sections that `wasm-ld` reads.
  - wasi-sdk's `wasm-ld` links it with wasi-libc and the libraries' objects.
  - For `wasm32-wasip2`, wasi-sdk's driver produces a component directly (the §5.4 probe's
    `clang` output was a component).
  - The alternative, the C code as a second core module in the same component sharing our memory,
    needs shared-memory linking and still one allocator, so it gains nothing.
- **Native.** The LLVM backend (#21) emits an object, and clang links it with the libraries and
  libc. The declaration's `c "symbol"` is an ordinary external symbol.
- **Both.** A relocatable object with external symbols is the common shape. So the Wasm FFI path
  and the native path are one design, which decision 25 asks for.

## 8. The trusted base, route by route

"Trusted" means that its correctness is assumed, not proved. **Safety** means the memory model
and the theorems. **Correctness** means the right bytes, the right server and the right time.

**Common to every route on WASI:**

- wasmtime 49.0.1: the engine, its compiler, and the canonical ABI's lift/lower, which covers
  safety;
- `wasmtime-wasi`'s implementations of the interfaces used (files, sockets, clocks, random), which
  cover correctness;
- the host OS;
- our allocator, trusted against its specification (SPEC §11: "The allocator is not an extern");
  this now includes `cabi_realloc` and, with FFI, `malloc`;
- the `wasi` package's extern implementations: canonical-ABI glue, each a row with its level;
- the `bcore:runner` interface and `bcc-run`, when the program uses them;
- `wasm-tools` (`component embed`/`new`), which writes the component's type information.

**Route 1 adds:**

- `wasmtime-wasi-http`, with hyper (HTTP/1.1, chunked decoding), for correctness;
- rustls and its crypto provider (ring, in the probe's build), for certificate verification and
  TLS, for correctness;
- `bcc-run`'s `send_request` hook: CA loading and connection set-up (the probe's version is
  about 70 lines), for correctness;
- the `Http`/`Body` extern contracts. All of this is outside our memory (§7.6).

**Route 2 adds**, removing hyper, rustls and the hook:

- BearSSL 0.6, **in-process**, for safety and correctness: the §7.6 hypothesis;
- the parts of wasi-libc BearSSL links (`memcpy`, `getentropy`, …), in-process, for safety;
- the BearSSL `foreign` declarations and their shims;
- wasi-sdk's clang and `wasm-ld`, for safety;
- entropy from `wasi:random` (host), for correctness.

Our HTTP/1.1 client is checked code and is not in the trusted base.

**Natively (P5):**

- the kernel;
- libc;
- the `posix` package's shims;
- BearSSL and every other linked C library, in-process: the §7.6 hypothesis, over the whole
  process;
- clang and lld;
- our allocator as `malloc`.

## 9. Prior art

Each entry quotes what was read, and says what this design takes or leaves.

- **WASI 0.2 and the component model** (WIT in wasmtime 49.0.1; the component-model Explainer).
  - Capabilities as resources: `wasi:sockets` "An opaque resource that represents access to (a
    subset of) the network. This enables context-based security for networking."
  - Filesystem authority is preopens only: `get-directories: func() ->
    list<tuple<descriptor, string>>`.
  - Handles: `own` is "a unique, opaque address of a resource that will be destroyed when this
    value is dropped", and `borrow` is "an opaque address of a resource that must be dropped
    before the current export call returns". That is our owned handle and our borrow for the
    call.
  - *Taken:* the preopen model for `Fs`, and the lend-for-the-call discipline.
  - *Left:* pollables as program-visible values, `input-stream`/`output-stream` resources, WASI's
    error enums and 0.3's async (§2.6).
- **Rust's `std::sys`** (the rust-src of rustc 1.97.1).
  - `library/std/src/sys/pal/mod.rs`: "The PAL (platform abstraction layer) contains
    platform-specific abstractions for implementing the features in the other submodules".
  - `sys/net/connection/mod.rs` selects `socket` for `all(target_os = "wasi", any(target_env =
    "p2", target_env = "p3"))` alongside Unix and Windows. So Rust implements WASI 0.2 sockets
    through the same `socket` module as Unix and Windows.
  - *Taken:* one interface, `cfg`-selected implementations (our packages), and the observation
    that WASI 0.2 is POSIX-shaped enough for one implementation to serve both.
  - *Left:* Rust's ambient authority. `std::fs::File::open` needs no capability.
- **Zig's `std.posix` and `std.Io`** (codeberg master, fetched 2026-09-30).
  - `std/posix.zig`: "POSIX API layer. This is more cross platform than using OS-specific APIs,
    however, it is lower-level and less portable than other namespaces such as `std.Io`", and
    "These APIs are generally lowered to libc function calls if and only if libc is linked".
  - `std/Io.zig`: "A cross-platform interface that abstracts all I/O operations and concurrency",
    a value with `vtable: *const VTable`, whose implementations include `Threaded`, and
    `Evented` (io_uring, kqueue or Dispatch, where `fiber.supported`).
  - C interop: `@cImport` "parses C code and imports the functions, types, variables, and
    compatible macro definitions". Of `[*c]T`, the docs say "This type is to be avoided whenever
    possible. The only valid reason for using a C pointer is in auto-generated code from
    translating C code."
  - *Taken:* an I/O interface passed as a value, and blocking or evented chosen by the
    implementation, which is Zig's answer to colouring.
  - *Left:* its run-time `vtable` dispatch (we specialize, §4.2); its fibers (stackful, which
    decision 25 excludes); and importing C headers wholesale (our declarations are written, with
    contracts).
- **Roc's platforms** (roc-lang.org/platforms).
  - "Every Roc application is built on exactly one platform, and that platform (not Roc's
    standard library) provides all of the application's I/O primitives."
  - "Because Roc's I/O primitives come from platforms, these mismatches can be prevented at build
    time."
  - "the host provides malloc and free implementations which the compiled Roc application will
    automatically call".
  - "the only way for Roc code to execute functions in other languages is if the selected platform
    offers a way to do that."
  - *Taken:* platform as a package providing the I/O, build-time mismatch errors (§4.2), and the
    host providing `malloc` (inverted in §7.4: we provide it to C).
  - *Left:* Roc's one platform per application with no capabilities inside it. Ours are
    capabilities, so authority within the program is still visible.
- **Austral** (the specification, "Capability-Based Security" and "Foreign Interfaces").
  - "The root of the capability hierarchy is a value of type `RootCapability`. This is the first
    argument to the entrypoint function".
  - On the FFI: "Ultimately, all guarantees are lost at the FFI boundary. … To use the FFI, a
    module has to be marked as unsafe using the `Unsafe_Module` pragma. … a list of unsafe modules
    in all dependencies (including transitive ones) can be collected by the build system."
  - *Taken:* capabilities as linear values from the entry point, and the build collecting the
    unsafe boundary (our generated trusted base).
  - *Left:* `Pointer[T]` in foreign signatures. Ours marshal modes instead.
- **Pony** (the tutorial, "Object Capabilities", "Trust Boundary", "Calling C", "Callbacks").
  - "Global variables are a form of what is called ambient authority."
  - `ponyc --safe=files:net:process` restricts which packages may use the C-FFI: "any other
    packages that try to use C-FFI calls will result in a compile-time error".
  - FFI declarations are checked at call sites, but "The compiler has no way to know what the
    native code expects and will just believe whatever you do."
  - Callbacks are "bare functions … with no receiver", passed with `addressof`.
  - *Taken:* a build-level trust boundary, and trampolines with no receiver (ours carry `ctx`).
- **Koka** (`lib/std/core/console.kk`, the book's grammar).
  - `extern xprintsln(s : string) : console ()` with per-backend bodies (`c "kk_println"`,
    `js "_println"`): an extern's type carries its effect.
  - *Taken:* the effect (for us, the capability) in the foreign declaration's type, and
    per-backend implementations of one declaration (our per-platform packages).
- **Effekt** (the language tour, "FFI").
  - "keep the FFI surface minimal … less foreign types and less foreign functions means more
    compatibility across backends".
  - "Since Effekt doesn't know anything about externs, you should manually annotate the capture
    of your extern function", with `io` "the default capture" and `async` for continuation
    capture.
  - *Taken:* `needs` (§7.2) is Effekt's capture annotation for C's own authority, and the rule
    that a callback cannot capture the continuation (§7.3) is its `async` distinction.
- **OCaml's Eio** (README).
  - "All authority starts at the (privileged) `Eio_main.run` function with the `env` parameter".
  - "`Eio_main` selects an appropriate backend (e.g. `eio_linux` or `eio_posix`), depending on
    your platform", and "For non-portable code you can use the platform-specific library
    directly".
  - Its advice: "it's clearer … to take the resources you need as separate arguments", and to pass
    `(fun () -> Eio.Net.connect net addr)` instead of `net`.
  - *Taken:* all of it. It is the closest existing design: capability I/O on an event loop, a
    portable API with backends selected at run time, and extensions named by package. We add
    linearity, and specialization in place of effects-with-fibers.
- **Go's `syscall` and netpoller** (`src/syscall/syscall.go`, `src/runtime/netpoll.go`).
  - "The primary use of syscall is inside other packages that provide a more portable interface
    to the system, such as "os", "time" and "net". Use those packages rather than this one if you
    can."
  - The netpoller's platform contract: "A particular implementation (epoll/kqueue/port/AIX/Windows)
    must define the following functions: `netpollinit` … `netpollopen(fd uintptr, pd *pollDesc)`
    … `netpoll(delta int64)`: Poll the network. If delta < 0, block indefinitely. If delta == 0,
    poll without blocking. If delta > 0, block for up to delta nanoseconds."
  - *Taken:* the readiness primitive with a deadline (§2.6's `wait`) as the whole platform
    contract for an event loop, and the syscall layer hidden below portable packages.

## 10. Staged plan

Each stage lands with its SPEC entry, proofs, library, lowering and running corpus programs, and
passes `scripts/ci-local.sh` (decision 17). "Probe" programs from §5 become corpus programs where
the gate can run them without network access.

| stage | SPEC | proofs | library | backend | runtime | delivers |
|---|---|---|---|---|---|---|
| **P1 Bundles and the simple capabilities** | a new entry after §11: bundles as records; `main`'s declared bundle; the ambient trigger generalized; `Args`, `Env`, exit status, `Clock`, `Random`, `Fs` (externs, opaque kinds, models); `IoError` (prov.); §12: host destructors as extern calls (§2.3); `withborS` at `opq` (§2.8) | a model and `*_meets` per kind (`Core/Stdio.lean`'s pattern); `externs_every_run` unchanged; `dtor_wf` with extern destructors | `lib/std` (the capability operations, `block_on`'s `sleep_until` as a blocking wait); the lend row for a record of cells (§2.8) | components: WASI 0.2 imports by canonical signature, `cabi_realloc` from our allocator, `wasm-tools` embed/new; stdio moved off `wasi_snapshot_preview1` | `bcc run` = `wasmtime run -W tail-call=y -S cli` with `--dir`/`--env` | §3.2 file copy, §3.3 env/args/exit, §3.4 timer |
| **P2 Net and the readiness interface** | `Net`, `Listener`, `Conn`; the platform interface (§2.6) as the package-internal level; `block_on` | models: a connection as the peer's script (bytes in, bytes out), as `Input`/`Output`; `Waiter` needs no model beyond "answers" | TCP operations over `try_*` + `wait`; HTTP/1.1 client and chunked decoding in our language (operator §1.5) | none new | `-S inherit-network`, `-S allow-ip-name-lookup` | §3.1 echo server; plain HTTP to `kubectl proxy` (operator milestone 2) |
| **P3 Http, Signals, and the first HTTPS request (route 1)** | `Http` as a capability with two handlers; `Body`; `TrustAnchors`; `Signals`/`Shutdown`; `bcore:runner` | models for `Body` (a byte script) and `Shutdown` (fires at most once) | `in_cluster`, `watch` (with generators, SPEC §15), `take_until` on shutdown | the `wasi` package's `Http` externs over `wasi:http` | **`bcc-run`**: wasmtime 49 embedder with the CA hook, the shutdown import, per-request timeouts | **§3.7 the HTTPS GET and §3.5 the watch stream, in-cluster** |
| **P4 FFI** | `foreign` declarations; the marshalling vocabulary (§7.2); `needs`, `allocates`; foreign handles; callbacks lent for the call | none new in the kernel: foreign functions are externs; the FP covers them under `ExternsMeet` | zlib bindings; `with_cstr` (strings design P15) | relocatable Wasm objects; C-ABI lowering of the vocabulary; trampolines (a table used by C only); `malloc` from our allocator | wasi-sdk in the toolchain; `bcc trusted` rows for foreign code | §3.6 zlib; BearSSL bindings (route 2 on WASI) |
| **P5 Native POSIX** | `posix` package; extensions `posix.Ext` | the same models (the packages share them) | route 2 as `posix`'s `Http` handler | the LLVM backend (#21); linking with clang | native binaries; `signalfd`/self-pipe; `openat2` or userspace confinement | every §3 program natively; HTTPS natively |
| later | threads; io_uring; the owned-buffer lowering (Q8); Windows | | a scheduler handler (#52), which needs no platform change | | | concurrent echo server; operator §6 step 10 |

**The first HTTPS request is P3.** It needs P1 (components, `Fs` for the token and CA, `Env`)
and P2's `Net` only for route 2. For route 1, P3 depends on P1 alone, so P3 can run in parallel
with P2 if HTTPS is wanted before the echo server. The probe of §5.2 already runs P3's platform
side. What remains is the language side and packaging `bcc-run`.

## 11. Open questions, with recommendations

Only questions with a real alternative. One-way doors are marked.

- **Q1. Handles as one-word values handed back, or as cells borrowed** (SPEC §11's `ref input`)?
  - Cells cost an allocation per handle and a borrow per call. Values cost nothing, and the
    surface `&mut conn` is the same.
  - *Recommendation:* values with move-and-rebind for every new handle kind. Keep the stdio cells
    until P1, then move them too if the corpus counts show the cell. Not a one-way door, since the
    surface is unchanged.
- **Q2. What does a failing destructor do?** (N6.)
  - *Recommendation:* drop the error in the implicit destructor. `close` returns it when called
    explicitly, and `linear` forbids forgetting. This is Rust's `Drop` choice, which the
    operator README records, plus an explicit path.
- **Q3. `Http`: a primitive capability, or an effect with handlers?**
  - *Recommendation:* an effect, with the library HTTP over `Net`+`Tls` as the portable handler
    and the host's HTTP as a second handler (§2.2). Making it a primitive would make `posix`'s
    implementation a foreign library (libcurl) and put HTTP in the trusted base natively.
- **Q4. How does route 1 receive the CA?**
  - *Recommendation:* `bcore:runner`'s `set-http-trust` import, called when the client is made,
    so the CA stays program data (§6.1). The alternative, a `bcc-run --ca` flag, makes the CA
    deployment configuration outside the program's types: simpler, but the program could no
    longer choose its trust.
- **Q5. Our own runner.**
  - *Recommendation:* build `bcc-run` at P3, pinned to one wasmtime version. Keep plain
    `wasmtime run` working for every program that needs neither shutdown nor custom trust. The
    cost is a Rust crate in the repository's toolchain, the size of the probe.
- **Q6. FFI linking in Wasm.**
  - *Recommendation:* the backend emits relocatable objects linked by `wasm-ld` (§7.7), which is
    also the native shape. This is one-way-ish: it changes the backend's output format.
- **Q7. Callbacks in the first FFI stage.**
  - *Recommendation:* lent-for-the-call only. Registration (stored callbacks) waits for a program
    that needs it: none of §3's does, and BearSSL needs none.
- **Q8. Borrowed buffers, or owned ones for completion-based I/O** (io_uring, IOCP)?
  - *Recommendation:* borrowed now (readiness on both platforms). When a completion backend
    lands, an owned variant lowers the same surface by move-and-rebind (§2.4). The surface is not
    a one-way door. The operation's type is, for code that names it, so the library exposes both
    shapes behind one surface call.
- **Q9. One `IoError`, or a type per capability?**
  - *Recommendation:* one, with `Other(i32)` for the platform's code, until #18 settles error
    rows. Per-capability types multiply conversions without a program needing them.
- **Q10. Exit.** Only `main`'s result, or also an `exit` operation?
  - *Recommendation:* only the result, so destructors run on every exit. A program that must stop
    at once returns from `main` through the error effect (#18) when it lands.
- **Q11. Directory confinement on POSIX.**
  - *Recommendation:* the contract promises confinement beneath a `Dir`, and `posix` implements
    it with `openat2(RESOLVE_BENEATH)` where available and userspace resolution elsewhere. The
    alternative, no promise on POSIX, makes `Fs` mean different things on the two platforms.
- **Q12. Run-time platform variants.**
  - *Recommendation:* dispatch inside the package on a start-up tag (§4.2), with compile-time
    selection as the constant-tag case. Specialize the program only where decision 35 already
    does.

## 12. What this document has not established

- I have not established that `bcc-run`'s trust import works as designed. The probe's embedder
  takes the CA from its command line, not from the guest through an import.
- I have not established that a `realloc` returning a lent view's address removes WASI's read
  copy (§2.4). It is untried.
- I have not established what WASI 0.3.1 changed from the 0.3.0 WIT I read.
- I have not established that the component model has no optional-import mechanism. I found none
  in the Explainer I read.
- I have not established that `withborS`'s proof goes through at `VTy.opq` (§2.8). I read only
  its restriction list.
- I have not established that mbedTLS builds for `wasm32-wasip2`. Only BearSSL and zlib were
  built.
- I have not established how wasi-libc's `malloc` would coexist with our allocator if we did not
  replace it (§7.4). The design replaces it, and the replacement is untried.
- I have not run anything natively, or on Windows. §4.4's POSIX and Windows columns are from the
  APIs' documented behaviour, not from probes.
- I have not established the cost of the per-call canonical-ABI copies at scale. The probes
  measured correctness, not throughput.
- I have not checked the behaviour of a Kubernetes cluster itself. The API server was a local
  stand-in with the same TLS, bearer-token and chunked-body shape.
