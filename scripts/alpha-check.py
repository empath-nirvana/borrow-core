#!/usr/bin/env python3
"""The renaming check: no elaboration identifies a variable by its name (SPEC §41, #617).

Every corpus program, and every library module, is renamed α-equivalently by `bcc alpha`: each
binder of a surface body gets a name of its own (`{x}q{k}`), and every name resolved to it the
same, so no binder shadows another and no two variables share a name. A program means what it
did, so `bcc check` must print the same up to the renaming and `bcc erase` the same erasure
(de Bruijn, so exactly the same). An elaboration that recognises a thing by its name, and so
worked only where two names coincided (a copy `let v = v` taken for `v`, #617), shows up as a
difference.

Two passes:

* `program`: each program renamed, the library as it is. The check's positions and names are
  mapped back through the renaming: a column on a renamed line, a name `{x}q{k}` to `x`, and a
  generated name that carries a position (`io_lb12_5_0`).
* `library`: every module of `lib/` renamed (`BCC_LIB`), each program as it is. A message from a
  module's code is printed at the module's position under the program's name, so columns are
  compared only up to the line; names are mapped back as above, and the original's renamed
  binders (`x1`) to the name they are written with.

`scripts/alpha-check.py [--jobs N] [--bcc BCC] [--alpha BCC] [--probes] [file…]`: every program
under `corpus/` (and the probes under `docs/expressiveness-probes/` with `--probes`), or the files
named. It fails on any difference, and prints each. `--alpha` renames with another build than the
one checked, to run the check on a build that has no `bcc alpha`.
"""
import argparse, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def run(bcc, args, env=None):
    p = subprocess.run([bcc] + args, capture_output=True, text=True, env=env, cwd=ROOT)
    return p.returncode, p.stdout + p.stderr


def renaming(bcc, f):
    """`bcc alpha --map f`: [(line, col, written, new, variable)], or None when it does not parse."""
    rc, out = run(bcc, ["alpha", "--map", f])
    if rc != 0:
        return None
    edits = []
    for l in out.splitlines():
        a = l.split(" ")
        edits.append((int(a[0]), int(a[1]), a[2], a[3], a[4]))
    return edits


WORD = re.compile(r"[A-Za-z0-9_']+")
POS = re.compile(r"(?<![\w.])(\d+):(\d+)")
GEN = re.compile(r"\b(io_[a-z]+)(\d+)_(\d+)")


class Back:
    """The renaming read backwards: names to the source's, columns to the source's."""

    def __init__(self, edits, names=None, cols=True):
        self.names = dict(names or {})
        self.lines = {}
        for (l, c, x, x2, _) in edits:
            self.names[x2] = x
            self.lines.setdefault(l, []).append((c, len(x), len(x2)))
        for l in self.lines:
            self.lines[l].sort()
        self.cols = cols

    def col(self, l, c):
        if not self.cols:
            return "_"
        d = 0
        for (oc, ol, nl) in self.lines.get(l, []):
            s = oc + d
            if c < s:
                break
            if c < s + nl:
                return str(oc)
            d += nl - ol
        return str(c - d)

    def text(self, s, cols=True):
        if cols:
            s = POS.sub(lambda m: f"{m.group(1)}:{self.col(int(m.group(1)), int(m.group(2)))}", s)
            s = GEN.sub(lambda m: f"{m.group(1)}{m.group(2)}_{self.col(int(m.group(2)), int(m.group(3)))}", s)
        elif not self.cols:
            s = POS.sub(lambda m: f"{m.group(1)}:_", s)
            s = GEN.sub(lambda m: f"{m.group(1)}{m.group(2)}__", s)
        return WORD.sub(lambda m: self.names.get(m.group(0), m.group(0)), s)


def same(cf, cg, back, backF):
    """The original's lines `cf` and the renamed program's `cg` agree up to the renaming. A
    position may also agree as it is: a position in a module's code is printed under the
    program's name, where the program's renaming does not apply."""
    lf, lg = cf.split("\n"), cg.split("\n")
    if len(lf) != len(lg):
        return False
    for a, b in zip(lf, lg):
        a = backF.text(a)
        if a == back.text(b):
            continue
        # Position by position: the text between positions up to the renaming, each position
        # mapped back or as it is.
        pa, pb = POS.split(a), POS.split(back.text(b, cols=False))
        if len(pa) != len(pb):
            return False
        for i in range(0, len(pa), 3):
            if pa[i] != pb[i]:
                return False
        for i in range(1, len(pa), 3):
            l, c = int(pb[i]), int(pb[i + 1])
            if pa[i] != pb[i] or pa[i + 1] not in (str(c), back.col(l, c)):
                return False
    return True


def compare(bcc, f, g, back, envG=None, backF=None):
    """`check` and `erase` of `f` and of its renamed `g`: the differences."""
    diffs = []
    backF = backF or Back([])
    rf, cf = run(bcc, ["check", f])
    rg, cg = run(bcc, ["check", g], envG)
    # The file's name is no variable's.
    cf, cg = cf.replace(f, "<file>"), cg.replace(g, "<file>")
    if rf != rg or not same(cf, cg, back, backF):
        diffs.append(f"check (exit {rf} / {rg}):\n--- {f}\n{backF.text(cf)}--- renamed\n{back.text(cg)}")
    if rf == 0:
        ef = run(bcc, ["erase", f])[1].replace(f, "<file>")
        eg = run(bcc, ["erase", g], envG)[1].replace(g, "<file>")
        if ef != eg:
            diffs.append("erase: the erasures differ")
    return diffs


def programs(probes):
    out = []
    dirs = ["corpus"] + (["docs/expressiveness-probes"] if probes else [])
    for d in dirs:
        for r, _, fs in os.walk(os.path.join(ROOT, d)):
            out += [os.path.relpath(os.path.join(r, x), ROOT) for x in fs if x.endswith(".bc")]
    return sorted(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--bcc", default=os.path.join(ROOT, ".lake/build/bin/bcc"))
    ap.add_argument("--probes", action="store_true")
    ap.add_argument("--alpha", help="the bcc that renames (default: --bcc), to check another build")
    ap.add_argument("files", nargs="*")
    a = ap.parse_args()
    files = a.files or programs(a.probes)
    ab = a.alpha or a.bcc
    tmp = tempfile.mkdtemp(prefix="alpha-")

    # The library renamed, and each module's renaming read backwards (names only).
    lib = os.path.join(tmp, "lib")
    os.makedirs(lib)
    libNames, libVars = {}, {}
    for m in sorted(os.listdir(os.path.join(ROOT, "lib"))):
        src = os.path.join("lib", m)
        if not m.endswith(".bc"):
            continue
        rc, out = run(ab, ["alpha", src])
        if rc != 0:
            print(f"{src}: bcc alpha failed:\n{out}")
            sys.exit(1)
        open(os.path.join(lib, m), "w").write(out)
        for (_, _, x, x2, v) in renaming(ab, src) or []:
            libNames[x2] = x
            if v != x:
                libVars[v] = x
    envLib = dict(os.environ, BCC_LIB=lib)

    def one(i_f):
        i, f = i_f
        diffs = []
        edits = renaming(ab, f)
        if edits is not None:
            g = os.path.join(tmp, f"p{i}", os.path.basename(f))
            os.makedirs(os.path.dirname(g))
            open(g, "w").write(run(ab, ["alpha", f])[1])
            diffs += ["program pass: " + d for d in compare(a.bcc, f, g, Back(edits))]
        # The library pass: the original's messages from module code name renamed binders as the
        # module writes them (`x1`), the renamed library's as `{x}q{k}`: both to `x`.
        back = Back([], libNames, cols=False)
        # A word the program writes is the program's (`fn c3` beside a module's renamed `c3`).
        own = set(WORD.findall(open(os.path.join(ROOT, f)).read()))
        rf = Back([], {v: x for v, x in libVars.items() if v not in own}, cols=False)
        diffs += ["library pass: " + d for d in compare(a.bcc, f, f, back, envLib, rf)]
        return f, diffs

    bad = 0
    with ThreadPoolExecutor(a.jobs) as ex:
        for f, diffs in ex.map(one, enumerate(files)):
            if diffs:
                bad += 1
                print(f"{f}: differs under renaming")
                for d in diffs:
                    print("  " + d.replace("\n", "\n  "))
    print(f"alpha-check: {len(files)} program(s), {bad} difference(s)")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
