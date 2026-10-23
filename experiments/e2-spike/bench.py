"""#682 B timing: each program natively through the new backend (`bcc compile --backend new
--target native`, then clang as `bcc run --native` builds it), against Rust; CPU time (user + sys)
of the child, the median of `--runs` interleaved runs after one warm-up. The core terms take their
sizes as constants, so each is copied to the work directory with the sizes substituted. The cached
form (`b2/cache_edit.py`) is the proven form's LLVM IR with its step replaced by hand: it is not
checked by anything.

    python3 experiments/e2-spike/bench.py [--runs 9] [--out DIR] [--only SUBSTR]
"""
import argparse, os, re, resource, statistics, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
BCC = os.path.join(ROOT, ".lake", "build", "bin", "bcc")
RUSTC = ["rustc", "--edition=2024", "-C", "opt-level=3", "-C", "embed-bitcode=no", "-C", "strip=debuginfo"]
N, T = 1048576, 8


def runtime_c():
    src = open(os.path.join(ROOT, "Backend", "Native", "Runtime.lean")).read()
    start = src.index('r##"', src.index("def runtimeC")) + 4
    return src[start:src.index('"##', start)]


def sized(path, n, tasks):
    s = open(path).read()
    s = re.sub(r"spawn0\(200, r\)", f"spawn0({n}, r)", s)
    s = re.sub(r"start_own\(200, r\)", f"start_own({n}, r)", s)
    s = s.replace("let n = 200;", f"let n = {n};").replace("let tasks = 3;", f"let tasks = {tasks};")
    return s


def emit_ll(name, src, out):
    bc = os.path.join(out, name + ".bc"); open(bc, "w").write(sized(src, N, T))
    ll = os.path.join(out, name + ".ll")
    r = subprocess.run([BCC, "compile", "--backend", "new", "--target", "native", bc, "-o", ll], capture_output=True)
    if r.returncode: sys.exit(f"bcc {name}: {r.stderr.decode()[:500]}")
    return ll


def link(name, ll, out, rt):
    exe = os.path.join(out, name)
    r = subprocess.run(["xcrun", "clang", "-O2", "-w", "-pthread", ll, rt, "-o", exe], capture_output=True)
    if r.returncode: sys.exit(f"clang {name}: {r.stderr.decode()[:500]}")
    return exe


def ours(name, rel, out, rt):
    return link(name, emit_ll(name, os.path.join(HERE, rel), out), out, rt)


def cached(name, rel, out, rt):
    ll = emit_ll(name + "-proven", os.path.join(HERE, rel), out)
    ed = os.path.join(out, name + ".ll")
    r = subprocess.run([sys.executable, os.path.join(HERE, "b2", "cache_edit.py"), ll, ed], capture_output=True)
    if r.returncode: sys.exit(f"cache_edit {name}: {r.stderr.decode()[:800]}")
    exe = os.path.join(out, name)
    r = subprocess.run(["xcrun", "clang", "-O2", "-flto", "-w", "-pthread", ed,
                        os.path.join(HERE, "b2", "cached_step.c"), rt, "-o", exe], capture_output=True)
    if r.returncode: sys.exit(f"clang {name}: {r.stderr.decode()[:500]}")
    return exe


def rust(name, rel, out):
    exe = os.path.join(out, name)
    r = subprocess.run(RUSTC + [os.path.join(HERE, rel), "-o", exe], capture_output=True)
    if r.returncode: sys.exit(f"rustc {name}: {r.stderr.decode()[:500]}")
    return exe


def cpu(cmd):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    r = subprocess.run(cmd, capture_output=True)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    if r.returncode: sys.exit(f"{cmd}: exit {r.returncode} {r.stderr.decode()[:300]}")
    t = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    return t * 1000, r.stdout.decode().split("\n")[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=9)
    ap.add_argument("--out", default=os.path.expanduser("~/repos/682b-work/bench"))
    ap.add_argument("--only", default="")
    a = ap.parse_args(); os.makedirs(a.out, exist_ok=True)
    rt = os.path.join(a.out, "runtime.c"); open(rt, "w").write(runtime_c())
    args = [str(N), str(T)]
    rows = [
        ("rs H3 task owns tree, Vec<&Node>", lambda: rust("rs-h3", "h3ref/main.rs", a.out), args + ["0"]),
        ("rs H3 build only", lambda: rust("rs-h3", "h3ref/main.rs", a.out), args + ["2"]),
        ("rs B1 main owns trees, tasks borrow, Vec<&Node>", lambda: rust("rs-b1", "b1_borrowed.rs", a.out), args + ["0"]),
        ("rs B1 build only", lambda: rust("rs-b1", "b1_borrowed.rs", a.out), args + ["2"]),
        ("rs B1 arena, tasks borrow, Vec<&ANode>", lambda: rust("rs-b1", "b1_borrowed.rs", a.out), args + ["3"]),
        ("rs B1 one shared tree, Vec<&Node>", lambda: rust("rs-b1", "b1_borrowed.rs", a.out), args + ["5"]),
        ("rs B1 one tree build only", lambda: rust("rs-b1", "b1_borrowed.rs", a.out), args + ["6"]),
        ("rs B1 arena build only", lambda: rust("rs-b1", "b1_borrowed.rs", a.out), args + ["4"]),
        ("main H3 src consume (task stacks)", lambda: ours("s3", "h3ref/src-owned-tree.bc", a.out, rt), []),
        ("main H3 build only", lambda: ours("b3", "h3ref/b3-build-only.bc", a.out, rt), []),
        ("B1 s1 surface arena, views held", lambda: ours("s1", "b1/s1-arena-held.bc", a.out, rt), []),
        ("B1 c1 core arena, views held, nu at 'd", lambda: ours("c1", "b1/c1-arena-held.bc", a.out, rt), []),
        ("B1 c1d core arena, views held, defun", lambda: ours("c1d", "b1/c1d-arena-held-defun.bc", a.out, rt), []),
        ("B1 c2s core one shared mu tree, root held, path", lambda: ours("c2s", "b1/c2s-mu-path-shared.bc", a.out, rt), []),
        ("B1 one mu tree build only", lambda: ours("b0s", "b1/b0s-one-tree-build-only.bc", a.out, rt), []),
        ("B1 arena build only", lambda: ours("b0", "b1/b0-arena-build-only.bc", a.out, rt), []),
        ("B2 p1 r3 owned mu, re-lend + path", lambda: ours("p1", "b2/p1-r3-owned-reborrow.bc", a.out, rt), []),
        ("B2 p1c r3 CACHED (unchecked LLVM edit)", lambda: cached("p1c", "b2/p1-r3-owned-reborrow.bc", a.out, rt), []),
        ("B2 p2 owned arena, re-lend + index", lambda: ours("p2", "b2/p2-arena-owned-reindex.bc", a.out, rt), []),
    ]
    rows = [r for r in rows if a.only in r[0] or r[0].startswith("rs H3 task")]
    cmds = []
    for label, mk, extra in rows:
        exe = mk()
        cmds.append((label, [exe] + extra))
    times = {l: [] for l, _ in cmds}; outs = {}
    for k in range(a.runs + 1):
        for label, cmd in cmds:
            t, o = cpu(cmd)
            if k: times[label].append(t)
            outs[label] = o
    for label, _ in cmds:
        ts = sorted(times[label])
        print(f"{label:48s} {statistics.median(ts):8.1f} ms  ({ts[0]:.1f}-{ts[-1]:.1f})  out {outs[label]}")


main()
