#!/usr/bin/env python3
"""The benchmark harness (`make bench`, issue #537).

Each benchmark is a directory `bench/<name>/` holding the same program three times: `main.bc`
(ours, built natively: `bcc compile --target native`, then `clang -O2` with the native runtime,
as `bcc run --native` builds it), `main.rs` (built as `cargo build --release` builds a binary:
the flags below are the ones cargo passes) and, where C is natural, `main.c` (`clang -O2`).
A benchmark's `args` file gives its arguments, and its `gen.py`, for one that reads standard
input, writes the input. Every side gets the same arguments and the same input; the sizes are
read at run time, so no compiler folds the work away.

For each benchmark and side: the build's time (ours split into `bcc` and `clang`), the size of
its machine code (`__TEXT,__text`) and of the executable stripped, and the run time as the
median of `--runs` runs after one warm-up, with the spread (the lowest and highest run). The
outputs of the sides must be equal (ours without the `main` value and `live` lines the runtime
prints after the output).

    python3 bench/bench.py [--runs N] [--only name,name]

writes `bench/out/results.md` (the table of `bench/README.md`) and `bench/out/results.json`.
"""
import argparse
import json
import os
import shutil
import statistics
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "bench")
OUT = os.path.join(BENCH, "out")
BCC = os.path.join(ROOT, ".lake", "build", "bin", "bcc")

RUSTC = ["rustc", "--edition=2024", "--crate-type", "bin", "-C", "opt-level=3",
         "-C", "embed-bitcode=no", "-C", "strip=debuginfo"]
CFLAGS = ["-O2", "-w"]
# What `bcc run --native` passes (`Backend/Driver.lean`, `clangArgs`).
BC_CFLAGS = ["-O2", "-w", "-pthread"]


# The order of the table: table A of #537 (where Rust is famously good), then table B (where we
# might beat it). A directory not listed comes last.
ORDER = ["sum", "prefix", "sieve", "sieve-for", "matmul", "quicksort", "chain-for", "chain-yield",
         "chain-gen", "sort-generic", "parse", "binary-trees", "n-body", "mandelbrot",
         "spectral-norm", "wordcount", "gen-tree", "gen-tree-dyn", "gen-tree-cb", "async-tree",
         "raise-small", "raise-large", "handlers-di", "handlers-di-generic"]


def benches():
    """Every directory of `bench/` with a `main.bc`: its `args` (one line, split at spaces) and
    its `gen.py`, when present, which writes the standard input to its standard output."""
    out = {}
    names = sorted(os.listdir(BENCH), key=lambda n: (ORDER.index(n) if n in ORDER else len(ORDER), n))
    for name in names:
        d = os.path.join(BENCH, name)
        if not os.path.isfile(os.path.join(d, "main.bc")):
            continue
        a = os.path.join(d, "args")
        args = open(a).read().split() if os.path.exists(a) else []
        g = os.path.join(d, "gen.py")
        out[name] = (args, g if os.path.exists(g) else None)
    return out


def run(cmd, **kw):
    t0 = time.perf_counter()
    r = subprocess.run(cmd, capture_output=True, **kw)
    return r, time.perf_counter() - t0


def stripped_size(exe):
    s = exe + ".stripped"
    shutil.copyfile(exe, s)
    subprocess.run(["strip", s], capture_output=True)
    n = os.path.getsize(s)
    os.remove(s)
    return n


def text_size(exe):
    """The bytes of the executable's machine code: its `__TEXT,__text` section."""
    r = subprocess.run(["size", "-m", exe], capture_output=True, text=True).stdout
    for line in r.splitlines():
        if "Section __text:" in line:
            return int(line.split(":")[1])
    return 0


def runtime_c():
    """The native runtime's C source, from `Backend/Native/Runtime.lean` (`runtimeC`)."""
    src = open(os.path.join(ROOT, "Backend", "Native", "Runtime.lean")).read()
    start = src.index('r##"', src.index("def runtimeC")) + 4
    return src[start:src.index('"##', start)]


def build(name, d, side, rt):
    """Build one side; (executable, build times) or raise."""
    exe = os.path.join(d, side)
    if side == "bc":
        ll = os.path.join(d, "main.ll")
        r, tb = run([BCC, "compile", "--target", "native",
                     os.path.join(BENCH, name, "main.bc"), "-o", ll])
        if r.returncode != 0:
            raise RuntimeError(f"bcc: {r.stderr.decode()[:2000]}")
        r, tc = run(["xcrun", "clang"] + BC_CFLAGS + [ll, rt, "-o", exe])
        if r.returncode != 0:
            raise RuntimeError(f"clang: {r.stderr.decode()[:2000]}")
        return exe, {"bcc": tb, "cc": tc, "total": tb + tc}
    if side == "rs":
        r, t = run(RUSTC + [os.path.join(BENCH, name, "main.rs"), "-o", exe])
        if r.returncode != 0:
            raise RuntimeError(f"rustc: {r.stderr.decode()[:2000]}")
        return exe, {"total": t}
    r, t = run(["xcrun", "clang"] + CFLAGS + [os.path.join(BENCH, name, "main.c"), "-lm", "-o", exe])
    if r.returncode != 0:
        raise RuntimeError(f"clang: {r.stderr.decode()[:2000]}")
    return exe, {"total": t}


def our_output(out):
    """Ours without the two lines the runtime prints after the program's output."""
    lines = out.split(b"\n")
    if len(lines) >= 3 and lines[-1] == b"" and lines[-2].startswith(b"live "):
        return b"\n".join(lines[:-3]) + b"\n"
    return out


def time_runs(exe, args, inp, runs):
    times = []
    outs = set()
    for k in range(runs + 1):
        t0 = time.perf_counter()
        r = subprocess.run([exe] + args, input=inp, capture_output=True)
        t = time.perf_counter() - t0
        if r.returncode != 0:
            raise RuntimeError(f"{exe} exited {r.returncode}: {r.stderr.decode()[:500]}")
        outs.add(r.stdout)
        if k > 0:
            times.append(t)
    if len(outs) != 1:
        raise RuntimeError(f"{exe}: output differs between runs")
    return times, outs.pop()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=11)
    ap.add_argument("--only", default="")
    a = ap.parse_args()
    all_benches = benches()
    names = [n for n in all_benches if not a.only or n in a.only.split(",")]
    os.makedirs(OUT, exist_ok=True)
    rt = os.path.join(OUT, "runtime.c")
    open(rt, "w").write(runtime_c())
    results = {}
    if a.only and os.path.exists(os.path.join(OUT, "results.json")):
        results = json.load(open(os.path.join(OUT, "results.json")))
    failed = 0
    for name in names:
        args, gen = all_benches[name]
        d = os.path.join(OUT, name)
        os.makedirs(d, exist_ok=True)
        inp = subprocess.run([sys.executable, gen], capture_output=True, check=True).stdout if gen else b""
        res = {"args": args, "sides": {}}
        outputs = {}
        for side, src in (("bc", "main.bc"), ("rs", "main.rs"), ("c", "main.c")):
            if not os.path.exists(os.path.join(BENCH, name, src)):
                continue
            try:
                exe, bt = build(name, d, side, rt)
                times, out = time_runs(exe, args, inp, a.runs)
            except RuntimeError as e:
                print(f"{name} [{side}]: {e}", file=sys.stderr)
                failed += 1
                continue
            outputs[side] = our_output(out) if side == "bc" else out
            res["sides"][side] = {
                "median": statistics.median(times), "min": min(times), "max": max(times),
                "build": bt, "size": os.path.getsize(exe), "stripped": stripped_size(exe),
                "text": text_size(exe)}
            print(f"{name} [{side}]: median {statistics.median(times)*1000:.1f} ms "
                  f"({min(times)*1000:.1f}-{max(times)*1000:.1f}), build {bt['total']:.2f} s, "
                  f"{os.path.getsize(exe)} bytes", flush=True)
        if len(set(outputs.values())) > 1:
            print(f"{name}: the outputs differ: " +
                  ", ".join(f"{s}={o[:80]!r}" for s, o in outputs.items()), file=sys.stderr)
            failed += 1
        results[name] = res
    json.dump(results, open(os.path.join(OUT, "results.json"), "w"), indent=1)
    open(os.path.join(OUT, "results.md"), "w").write(table(results))
    print(table(results))
    return 1 if failed else 0


def ms(x):
    return f"{x*1000:.0f}" if x >= 0.1 else f"{x*1000:.1f}"


def kb(n):
    return f"{n/1024:.1f}K" if n < 10240 else f"{n/1024:.0f}K"


def table(results):
    rows = ["| benchmark | ours ms (spread) | Rust ms (spread) | C ms (spread) | ours/Rust | ours/C "
            "| code ours / Rust / C | file ours / Rust / C | build ours (bcc + clang) / Rust / C s |",
            "|---|---|---|---|---|---|---|---|---|"]
    for name in sorted(results, key=lambda n: (ORDER.index(n) if n in ORDER else len(ORDER), n)):
        s = results[name]["sides"]

        def cell(k):
            if k not in s:
                return "—"
            return f"{ms(s[k]['median'])} ({ms(s[k]['min'])}–{ms(s[k]['max'])})"

        def ratio(k):
            if "bc" not in s or k not in s:
                return "—"
            return f"{s['bc']['median'] / s[k]['median']:.2f}×"

        size = " / ".join(kb(s[k]["stripped"]) if k in s else "—" for k in ("bc", "rs", "c"))
        code = " / ".join(kb(s[k].get("text", 0)) if k in s else "—" for k in ("bc", "rs", "c"))
        b = s.get("bc", {}).get("build")
        bo = f"{b['total']:.2f} ({b['bcc']:.2f} + {b['cc']:.2f})" if b else "—"
        bt = " / ".join([bo] + [f"{s[k]['build']['total']:.2f}" if k in s else "—" for k in ("rs", "c")])
        rows.append(f"| {name} | {cell('bc')} | {cell('rs')} | {cell('c')} | {ratio('rs')} | "
                    f"{ratio('c')} | {code} | {size} | {bt} |")
    return "\n".join(rows) + "\n"


if __name__ == "__main__":
    sys.exit(main())
