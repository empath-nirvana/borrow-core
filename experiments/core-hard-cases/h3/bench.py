"""H1/H3 timing: each program natively through the new backend (`bcc compile --backend new
--target native`, then clang as `bcc run --native` builds it), against Rust, CPU time (user + sys)
of the child, the median of `--runs` interleaved runs after one warm-up. The core terms take their
sizes as constants, so each is copied to the work directory with the sizes substituted.

    python3 experiments/core-hard-cases/h3/bench.py [--runs 7] [--out DIR]
"""
import argparse, os, re, resource, statistics, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
BCC = os.path.join(ROOT, ".lake", "build", "bin", "bcc")
HERE = os.path.dirname(os.path.abspath(__file__))
H1 = os.path.join(os.path.dirname(HERE), "h1")
RUSTC = ["rustc", "--edition=2024", "-C", "opt-level=3", "-C", "embed-bitcode=no", "-C", "strip=debuginfo"]

def runtime_c():
    src = open(os.path.join(ROOT, "Backend", "Native", "Runtime.lean")).read()
    start = src.index('r##"', src.index("def runtimeC")) + 4
    return src[start:src.index('"##', start)]

def sized(src, n, tasks):
    s = open(src).read()
    s = re.sub(r"spawn0\(200, r\)", f"spawn0({n}, r)", s)
    s = s.replace("let n = 200;", f"let n = {n};").replace("let tasks = 3;", f"let tasks = {tasks};")
    s = s.replace("let reps = 2;", f"let reps = {tasks};")
    return s

def build_ours(name, src, n, tasks, out, rt):
    bc = os.path.join(out, name + ".bc"); open(bc, "w").write(sized(src, n, tasks))
    ll = os.path.join(out, name + ".ll"); exe = os.path.join(out, name)
    r = subprocess.run([BCC, "compile", "--backend", "new", "--target", "native", bc, "-o", ll], capture_output=True)
    if r.returncode: sys.exit(f"bcc {name}: {r.stderr.decode()[:500]}")
    r = subprocess.run(["xcrun", "clang", "-O2", "-w", "-pthread", ll, rt, "-o", exe], capture_output=True)
    if r.returncode: sys.exit(f"clang {name}: {r.stderr.decode()[:500]}")
    return [exe]

def build_rs(name, src, out):
    exe = os.path.join(out, name)
    r = subprocess.run(RUSTC + [src, "-o", exe], capture_output=True)
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
    ap = argparse.ArgumentParser(); ap.add_argument("--runs", type=int, default=7)
    ap.add_argument("--out", default=os.path.expanduser("~/repos/669h-work/h3/bench"))
    a = ap.parse_args(); os.makedirs(a.out, exist_ok=True)
    rt = os.path.join(a.out, "runtime.c"); open(rt, "w").write(runtime_c())
    N, T = 1048576, 8
    rows = [
        ("H3 rs borrow (stack of &Node)", build_rs("rs", os.path.join(HERE, "main.rs"), a.out), [str(N), str(T), "0"]),
        ("H3 rs consume", None, [str(N), str(T), "1"]),
        ("H3 rs build only", None, [str(N), str(T), "2"]),
        ("H3 core r3 re-borrow per step", build_ours("r3", os.path.join(HERE, "r3-owned-tree-reborrow.bc"), N, T, a.out, rt), []),
        ("H3 core z3 consume, frames array", build_ours("z3", os.path.join(HERE, "z3-owned-tree-consume.bc"), N, T, a.out, rt), []),
        ("H3 core zz3 zipper, owned, rebuilt", build_ours("zz3", os.path.join(HERE, "zz3-owned-tree-zipper.bc"), N, T, a.out, rt), []),
        ("H3 main src consume (task stacks)", build_ours("s3", os.path.join(HERE, "src-owned-tree.bc"), N, T, a.out, rt), []),
        ("H3 core b3 build only", build_ours("b3", os.path.join(HERE, "b3-build-only.bc"), N, T, a.out, rt), []),
        ("H1 rs bench/async-tree (iterative)", build_rs("rs-at", os.path.join(ROOT, "bench", "async-tree", "main.rs"), a.out), ["1048576", "28"]),
        ("H1 core a1 frames mu list", build_ours("a1", os.path.join(H1, "a1-async-tree.bc"), 1048576, 28, a.out, rt), []),
        ("H1 core a1b frames array", build_ours("a1b", os.path.join(H1, "a1b-async-tree-array.bc"), 1048576, 28, a.out, rt), []),
        ("H1 main src async-tree (task stacks)", build_ours("sat", os.path.join(H1, "src-async-tree.bc"), 1048576, 28, a.out, rt), []),
        ("H1 rs bench/gen-tree", build_rs("rs-gt", os.path.join(ROOT, "bench", "gen-tree", "main.rs"), a.out), ["1048576", "60"]),
        ("H1 core g1 gen-tree at its for", build_ours("g1", os.path.join(H1, "g1-gen-tree-for.bc"), 1048576, 60, a.out, rt), []),
        ("H1 main src gen-tree", build_ours("sgt", os.path.join(H1, "src-gen-tree.bc"), 1048576, 60, a.out, rt), []),
        ("H1 core g2 zip, stored, frames mu list", build_ours("g2", os.path.join(H1, "g2-gen-zip-stored.bc"), 1048576, 4, a.out, rt), []),
        ("H1 main src zip (stored generators)", build_ours("sgz", os.path.join(H1, "src-gen-zip.bc"), 1048576, 4, a.out, rt), []),
    ]
    cmds = []
    last = None
    for label, exe, args in rows:
        if isinstance(exe, list): exe = exe[0]
        if exe is None: exe = last
        last = exe
        cmds.append((label, [exe] + args))
    times = {l: [] for l, _ in cmds}; outs = {}
    for k in range(a.runs + 1):
        for label, cmd in cmds:
            t, o = cpu(cmd)
            if k: times[label].append(t)
            outs[label] = o
    for label, _ in cmds:
        ts = sorted(times[label])
        print(f"{label:42s} {statistics.median(ts):8.1f} ms  ({ts[0]:.1f}-{ts[-1]:.1f})  out {outs[label]}")

main()
