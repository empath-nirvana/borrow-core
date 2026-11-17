#!/usr/bin/env python3
"""The gate's result cache: a recorded pass is replayed instead of run, for byte-identical inputs.

A *unit* is one unit of work a gate step already has: one job of one `par` call (scripts/par.sh:
a program, a block, a pair), or a whole step where the step is not per-program. A unit's key is a
sha256 over everything it reads:

  * the step's name and its mode (the flags and exported variables its script passes in
    `PAR_CACHE`, or the command line of a whole step);
  * every file under scripts/ (the step's script and everything it sources or runs) and the
    Makefile;
  * the tools: `uname -sm`, the Python running this, wasmtime (path and `--version`), and the C
    compiler `bcc cc` resolves to with its `--version`;
  * the environment variables `BC_*`, `BCC_*` and `CI_LOCAL_*` (but `CI_LOCAL_BUILT` and
    `CI_LOCAL_BASE`, which choose only whether and what to build), and `source_digest`
    (scripts/source-stage.sh's interpreter digest);
  * for a unit that runs the compiler (`bcc` class): the binaries (`.lake/build/bin/bcc`,
    `bcc-counts`, and every binary the variables `bcc`, `bccCounts`, `counts`, `BCC` name), each
    by content, and the library each reads (`lib/` of the checkout whose `.lake/build/bin/` holds
    it, as `Frontend/Sugar.lean`'s `libDir` finds it, or `$BCC_LIB`);
  * for a unit that reads the Lean sources (`lean` class): every `.lean` file under the
    repository (outside `.lake/` and `.git/`), `lakefile.toml`, `lake-manifest.json` and
    `lean-toolchain`;
  * the unit's own files (`deps` below), each by path and content, and the absence of each
    sidecar it may read.

The store is `${GATE_CACHE_DIR:-$HOME/repos/.gate-cache}/<step>/<key>/`, shared by every worktree:
`out` (the unit's standard output and error) and `side/` (the files the unit hands back to its
script, scripts/par.sh's `$PAR_SIDE`). Only passes are stored; a unit that marks itself
(`par_nostore`, or `$GATE_CACHE_NOSTORE` for a whole step) is not, as one that ran the source
interpreter or wrote a key. An entry is written under a temporary name in the same directory and
renamed, so a reader sees a whole entry or none. `GATE_CACHE=0` reads and writes nothing.

    gate_cache.py par-start DIR FN       (scripts/par.sh) keys, hits replayed into DIR, misses printed
    gate_cache.py par-finish DIR FN      store the passing misses, collect side files, print in order
    gate_cache.py step ID CLASS [--files F…] -- CMD…   a whole step, run or replayed
    gate_cache.py step-key ID CLASS [--files F…] -- CMD…   the key `step` would use
    gate_cache.py tools                  the tools line (ci-local exports it as GATE_CACHE_TOOLS)
"""
import hashlib, os, re, shutil, subprocess, sys, tempfile

sys.dont_write_bytecode = True
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VERSION = "gate-cache 1"


def enabled():
    return os.environ.get("GATE_CACHE", "1") != "0"


def store_dir():
    return os.environ.get("GATE_CACHE_DIR") or os.path.join(os.path.expanduser("~"), "repos", ".gate-cache")


_hashes = {}


def sha_file(p):
    """The sha256 of file p's bytes, or `absent`."""
    ap = os.path.abspath(p)
    if ap in _hashes:
        return _hashes[ap]
    try:
        h = hashlib.sha256()
        with open(ap, "rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
        d = h.hexdigest()
    except (FileNotFoundError, IsADirectoryError, NotADirectoryError):
        d = "absent"
    _hashes[ap] = d
    return d


def walk(d, prune=(".git", ".lake", "__pycache__")):
    """Every file under directory d (relative to ROOT), sorted."""
    out = []
    top = os.path.join(ROOT, d)
    for r, ds, fs in os.walk(top):
        ds[:] = sorted(x for x in ds if x not in prune)
        for f in fs:
            if f.endswith(".pyc"):
                continue
            out.append(os.path.relpath(os.path.join(r, f), ROOT))
    return sorted(out)


def files_lines(tag, paths):
    return [f"{tag} {p} {sha_file(os.path.join(ROOT, p))}" for p in paths]


def tools_line():
    """`uname -sm`, Python, wasmtime and the C compiler `bcc cc` names, with their versions."""
    env = os.environ.get("GATE_CACHE_TOOLS")
    if env:
        return env
    parts = [" ".join(os.uname()[i] for i in (0, 4)), "python " + sys.version.split()[0]]

    def out(cmd):
        try:
            p = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT, timeout=120)
            return f"{p.returncode} {(p.stdout + p.stderr).strip()}"
        except (OSError, subprocess.TimeoutExpired) as e:
            return f"error {e}"

    w = shutil.which("wasmtime")
    parts.append(f"wasmtime {w} {out([w, '--version']) if w else '-'}")
    bcc = os.path.join(ROOT, ".lake/build/bin/bcc")
    cc = out([bcc, "cc"]) if os.path.exists(bcc) else "no bcc"
    parts.append(f"cc {cc}")
    if cc.startswith("0 "):
        parts.append(f"cc-version {out(cc[2:].split() + ['--version'])}")
    return " | ".join(parts).replace("\n", " ")


ENV_SKIP = {"CI_LOCAL_BUILT", "CI_LOCAL_BASE"}


def env_lines():
    out = []
    for k in sorted(os.environ):
        if (re.match(r"^(BC_|BCC_|CI_LOCAL_)", k) and k not in ENV_SKIP) or k == "source_digest":
            out.append(f"env {k}={os.environ[k]}")
    return out


def lib_of(binary):
    """The library directory `binary` reads (`Frontend/Sugar.lean`, `libDir`)."""
    if os.environ.get("BCC_LIB"):
        return os.environ["BCC_LIB"]
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(binary)))))
    if os.path.exists(os.path.join(root, "lib", "prelude.bc")):
        return os.path.join(root, "lib")
    return os.path.join(ROOT, "lib")


def binaries(extra=()):
    bs = [os.path.join(ROOT, ".lake/build/bin/bcc"), os.path.join(ROOT, ".lake/build/bin/bcc-counts")]
    bs += [os.path.join(ROOT, b) for b in extra if b]
    for v in ("bcc", "bccCounts", "counts", "BCC"):
        p = os.environ.get(v)
        if p and os.path.isfile(os.path.join(ROOT, p)):
            bs.append(os.path.join(ROOT, p))
    seen, out = set(), []
    for b in bs:
        b = os.path.realpath(b)
        if b not in seen:
            seen.add(b)
            out.append(b)
    return out


def class_lines(cls, extra=()):
    lines = []
    if "bcc" in cls.split(","):
        libs = set()
        for b in binaries(extra):
            lines.append(f"bin {b} {sha_file(b)}")
            libs.add(os.path.realpath(lib_of(b)))
        for l in sorted(libs):
            for r, _, fs in os.walk(l):
                for f in sorted(fs):
                    p = os.path.join(r, f)
                    lines.append(f"lib {os.path.relpath(p, l)} {sha_file(p)}")
    if "lean" in cls.split(","):
        lean = [p for p in walk(".") if p.endswith(".lean")]
        lines += files_lines("lean", lean)
        lines += files_lines("config", ["lakefile.toml", "lake-manifest.json", "lean-toolchain"])
    return lines


def base_lines(step, cls, extra=()):
    lines = [VERSION, f"step {step}", f"class {cls}"]
    lines += files_lines("script", walk("scripts") + ["Makefile"])
    lines.append("tools " + tools_line())
    lines += env_lines()
    lines += class_lines(cls, extra)
    return lines


def digest(lines):
    return hashlib.sha256("\n".join(lines).encode()).hexdigest()


# --- the files of one `par` unit ------------------------------------------------------------

_listings = {}


def listing(d):
    if d not in _listings:
        try:
            _listings[d] = sorted(os.listdir(os.path.join(ROOT, d)))
        except OSError:
            _listings[d] = []
    return _listings[d]


_tables = None


def tables():
    """Every corpus/*.expected table's lines, by their first field."""
    global _tables
    if _tables is None:
        _tables = {}
        for t in listing("corpus"):
            if not t.endswith(".expected"):
                continue
            rows = {}
            with open(os.path.join(ROOT, "corpus", t), encoding="utf-8", errors="surrogateescape") as fh:
                for line in fh:
                    w = line.split(None, 1)
                    if w:
                        rows.setdefault(w[0], []).append(line.rstrip("\n"))
            _tables[t] = rows
    return _tables


def stem_of(p):
    b = os.path.basename(p)
    for ext in (".core.bc", ".lowered.bc", ".bc", ".txt"):
        if b.endswith(ext):
            return b[: -len(ext)]
    return b.rsplit(".", 1)[0]


def corpus_deps(p):
    """A corpus unit's files: the file; every file beside it with its stem (`.in .args .out .err
    .status .key` …); the same stem's files in corpus/, corpus/reports/, corpus/trusted/ and
    corpus/copies/ (a reports file's program, a program's reports); and its rows in every
    corpus/*.expected table (by its name under corpus/, or its path)."""
    lines = [f"arg {p}"]
    s = stem_of(p)
    files = {p}
    for d in {os.path.dirname(p), "corpus", "corpus/reports", "corpus/trusted", "corpus/copies"}:
        for f in listing(d):
            if f.startswith(s + "."):
                files.add(os.path.join(d, f) if d else f)
    lines += files_lines("file", sorted(files))
    name = p[len("corpus/"):] if p.startswith("corpus/") else p
    name = name[:-3] if name.endswith(".bc") else name
    for t, rows in sorted(tables().items()):
        for k in (name, p, p + ":"):
            for r in rows.get(k, []):
                lines.append(f"row {t} {r}")
    return lines


def sugar_deps(p):
    """A sugar pair (scripts/check-sugar.sh): the sugared file and its core form (named on its first
    line, `-- core: <other>`, else `<name>.core.bc`), or a lowering and the program it lowers."""
    lines = [f"arg {p}"]
    first = ""
    try:
        with open(os.path.join(ROOT, p), encoding="utf-8", errors="surrogateescape") as fh:
            first = fh.readline().rstrip("\n")
    except OSError:
        pass
    files = [p]
    if p.endswith(".lowered.bc"):
        if first.startswith("-- lowers: "):
            files.append(first[len("-- lowers: "):])
    elif first.startswith("-- core: "):
        files.append(os.path.join(os.path.dirname(p), first[len("-- core: "):]))
    else:
        files.append(p[:-3] + ".core.bc")
    return lines + files_lines("file", files)


_keylines = None


def book_deps(n):
    """A book block (scripts/book-doctest.sh): its manifest line (attributes, chapter, line), its
    text by content, and every recorded keys line that starts with its block hash."""
    global _keylines
    tmp = os.environ["tmp"]
    attrs, md, line = "", "", ""
    with open(os.path.join(tmp, "manifest"), encoding="utf-8", errors="surrogateescape") as fh:
        for l in fh:
            w = l.rstrip("\n").split("\t")
            if w[0] == n:
                attrs, md, line = w[1], w[2], w[3]
                break
    f = os.path.join(tmp, f"{n}.bc")
    with open(f, "rb") as fh:
        text = fh.read()
    bh = hashlib.sha256(attrs.encode() + b"\n" + text).hexdigest()
    if _keylines is None:
        _keylines = {}
        for p in walk("book/keys"):
            with open(os.path.join(ROOT, p), encoding="utf-8", errors="surrogateescape") as fh:
                for l in fh:
                    _keylines.setdefault(l.split(" ", 1)[0], []).append(l.rstrip("\n"))
    lines = [f"block {attrs}\t{md}\t{line}", f"text {hashlib.sha256(text).hexdigest()}"]
    return lines + [f"key {l}" for l in sorted(_keylines.get(bh, []))]


def unit_deps(mode, arg):
    if mode == "corpus":
        return corpus_deps(arg)
    if mode == "sugar":
        return sugar_deps(arg)
    if mode == "book":
        return book_deps(arg)
    if mode.startswith("files:"):
        fs = sorted(set(mode[len("files:"):].split()))
        return [f"arg {arg}"] + files_lines("file", fs)
    raise SystemExit(f"gate_cache: unknown dependency mode {mode}")


# --- the store --------------------------------------------------------------------------------

def entry(step, key):
    return os.path.join(store_dir(), re.sub(r"[^A-Za-z0-9_.-]+", "_", step), key)


def put(step, key, out_file, side_dir=None):
    """Record a pass: `out` and `side/`, written under a temporary name and renamed."""
    final = entry(step, key)
    if os.path.isdir(final):
        return
    parent = os.path.dirname(final)
    os.makedirs(parent, exist_ok=True)
    t = tempfile.mkdtemp(prefix=".tmp.", dir=parent)
    try:
        shutil.copyfile(out_file, os.path.join(t, "out"))
        if side_dir and os.path.isdir(side_dir):
            shutil.copytree(side_dir, os.path.join(t, "side"))
        os.rename(t, final)
    except OSError:
        shutil.rmtree(t, ignore_errors=True)


def stat(replayed, ran):
    s = os.environ.get("GATE_CACHE_STATS")
    if s and (replayed or ran):
        with open(s, "a") as fh:
            fh.write(f"{replayed} {ran}\n")


# --- par --------------------------------------------------------------------------------------

def par_start(d, fn):
    """Read DIR/jobs (`i` and `arg`, a line each); for each hit, write DIR/i.out, DIR/i.rc and
    DIR/i.side as the run would have; print the misses (`i` and `arg`, a line each) for xargs."""
    with open(os.path.join(d, "jobs"), encoding="utf-8", errors="surrogateescape") as fh:
        ws = fh.read().split("\n")
    jobs = [(ws[k], ws[k + 1]) for k in range(0, len(ws) - 1, 2)]
    spec = os.environ.get("PAR_CACHE", "")
    if not spec or not enabled():
        for i, a in jobs:
            sys.stdout.write(f"{i}\n{a}\n")
        return
    mode = os.environ.get("PAR_CACHE_DEPS", "corpus")
    step = spec.split()[0]
    base = base_lines(spec, "bcc") + [f"fn {fn}", f"deps {mode}"]
    keys = []
    for i, a in jobs:
        k = digest(base + unit_deps(mode, a))
        keys.append(f"{i} {k}")
        e = entry(step, k)
        if os.path.isdir(e):
            try:
                shutil.copyfile(os.path.join(e, "out"), os.path.join(d, f"{i}.out"))
                if os.path.isdir(os.path.join(e, "side")):
                    shutil.copytree(os.path.join(e, "side"), os.path.join(d, f"{i}.side"), dirs_exist_ok=True)
                with open(os.path.join(d, f"{i}.rc"), "w") as fh:
                    fh.write("0\n")
                with open(os.path.join(d, f"{i}.hit"), "w"):
                    pass
                continue
            except OSError:
                for x in (f"{i}.out", f"{i}.rc", f"{i}.hit"):
                    try:
                        os.remove(os.path.join(d, x))
                    except OSError:
                        pass
                shutil.rmtree(os.path.join(d, f"{i}.side"), ignore_errors=True)
                os.makedirs(os.path.join(d, f"{i}.side"), exist_ok=True)
        sys.stdout.write(f"{i}\n{a}\n")
    with open(os.path.join(d, "keys"), "w") as fh:
        fh.write("\n".join(keys) + "\n")


def append_tree(src, dst):
    """Append every file under src to the file of the same relative path under dst."""
    for r, _, fs in os.walk(src):
        for f in sorted(fs):
            s = os.path.join(r, f)
            t = os.path.join(dst, os.path.relpath(s, src))
            os.makedirs(os.path.dirname(t), exist_ok=True)
            with open(s, "rb") as a, open(t, "ab") as b:
                shutil.copyfileobj(a, b)


def par_finish(d, fn):
    """Store each miss that passed (and did not mark itself `nostore`); append each job's side
    files to $PAR_COLLECT in job order; print each job's output in order; exit with the number of
    jobs that failed (at most 255 are told apart, as the caller reads only zero or not)."""
    with open(os.path.join(d, "jobs"), encoding="utf-8", errors="surrogateescape") as fh:
        ws = fh.read().split("\n")
    n = len(ws) // 2
    keys = {}
    kp = os.path.join(d, "keys")
    if os.path.exists(kp):
        for l in open(kp):
            w = l.split()
            if len(w) == 2:
                keys[w[0]] = w[1]
    spec = os.environ.get("PAR_CACHE", "")
    step = spec.split()[0] if spec else ""
    collect = os.environ.get("PAR_COLLECT", "")
    failed = replayed = ran = 0
    out = sys.stdout.buffer
    for j in range(1, n + 1):
        i = str(j)
        o = os.path.join(d, f"{i}.out")
        try:
            rc = open(os.path.join(d, f"{i}.rc")).read().strip()
        except OSError:
            rc = "1"
        hit = os.path.exists(os.path.join(d, f"{i}.hit"))
        side = os.path.join(d, f"{i}.side")
        if keys and enabled():
            if hit:
                replayed += 1
            else:
                ran += 1
                if rc == "0" and i in keys and not os.path.exists(os.path.join(d, f"{i}.nostore")):
                    put(step, keys[i], o, side)
        if collect and os.path.isdir(side):
            append_tree(side, collect)
        try:
            with open(o, "rb") as fh:
                shutil.copyfileobj(fh, out)
        except OSError:
            out.write(f"par: job {j} ({fn}) did not run\n".encode())
        if rc != "0":
            failed += 1
    out.flush()
    stat(replayed, ran)
    with open(os.path.join(d, "failed"), "w") as fh:
        fh.write(f"{failed}\n")


# --- a whole step -----------------------------------------------------------------------------

def step_args(argv):
    """`ID CLASS [--files F…] -- CMD…`: the step's id, its key, and CMD."""
    sid, cls = argv[0], argv[1]
    rest = argv[2:]
    files = []
    if rest and rest[0] == "--files":
        k = rest.index("--")
        files = rest[1:k]
        rest = rest[k:]
    if not rest or rest[0] != "--" or len(rest) < 2:
        raise SystemExit("usage: gate_cache.py step ID CLASS [--files F…] -- CMD…")
    cmd = rest[1:]
    if not enabled():
        return sid, None, cmd
    paths = []
    for f in files:
        if os.path.isdir(os.path.join(ROOT, f)):
            paths += walk(f)
        else:
            paths.append(f)
    lines = base_lines(sid, cls) + [f"cmd {' '.join(cmd)}"] + files_lines("file", sorted(set(paths)))
    return sid, digest(lines), cmd


def step(argv):
    """`step ID CLASS [--files F…] -- CMD…`: the step's recorded pass, or CMD run (with
    GATE_CACHE_INNER=ID, so a script that wraps itself runs its body) and its pass recorded. The
    key covers the class's inputs (`bcc`: the binaries and the library; `lean`: the Lean sources
    and the Lake configuration), scripts/, the tools, the environment, CMD and the files (or every
    file under the directories) named."""
    sid, key, cmd = step_args(argv)
    env = dict(os.environ, GATE_CACHE_INNER=sid)
    if key is None:
        os.chdir(ROOT)
        os.execvpe(cmd[0], cmd, env)
    e = entry(sid, key)
    if os.path.isdir(e):
        with open(os.path.join(e, "out"), "rb") as fh:
            shutil.copyfileobj(fh, sys.stdout.buffer)
        sys.stdout.flush()
        stat(1, 0)
        return 0
    t = tempfile.mkdtemp(prefix="gate-cache-")
    try:
        log = os.path.join(t, "out")
        env["GATE_CACHE_NOSTORE"] = os.path.join(t, "nostore")
        with open(log, "wb") as lf:
            p = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            for chunk in iter(lambda: p.stdout.read1(65536), b""):
                lf.write(chunk)
                sys.stdout.buffer.write(chunk)
                sys.stdout.flush()
            rc = p.wait()
        stat(0, 1)
        if rc == 0 and not os.path.exists(env["GATE_CACHE_NOSTORE"]):
            put(sid, key, log)
        return rc
    finally:
        shutil.rmtree(t, ignore_errors=True)


def wrap_self(sid, cls, files=()):
    """For a Python script: run the rest of the script under `step`, unless already inside it."""
    if os.environ.get("GATE_CACHE_INNER") == sid or not enabled():
        return
    script = os.path.relpath(os.path.abspath(sys.argv[0]), ROOT)
    argv = [sid, cls] + (["--files", *files] if files else []) + ["--", "python3", script, *sys.argv[1:]]
    sys.stdout.flush()
    sys.exit(step(argv))


# --- for a script that keeps its own units (scripts/alpha-check.py) ---------------------------

class Units:
    """Keys of one step's units, computed with the same base as `par`."""

    def __init__(self, spec, mode="corpus", cls="bcc", bins=()):
        self.on = enabled()
        self.step = spec.split()[0]
        self.base = base_lines(spec, cls, bins) + [f"deps {mode}"] if self.on else []
        self.mode = mode
        self.replayed = self.ran = 0

    def key(self, arg):
        return digest(self.base + unit_deps(self.mode, arg)) if self.on else None

    def hit(self, key):
        return self.on and key is not None and os.path.isdir(entry(self.step, key))

    def pass_(self, key, text=""):
        if not self.on or key is None:
            return
        t = tempfile.mkdtemp(prefix="gate-cache-")
        try:
            o = os.path.join(t, "out")
            with open(o, "w") as fh:
                fh.write(text)
            put(self.step, key, o)
        finally:
            shutil.rmtree(t, ignore_errors=True)

    def done(self):
        if self.on:
            stat(self.replayed, self.ran)


def main():
    a = sys.argv[1:]
    if not a:
        print(__doc__)
        return 2
    if a[0] == "par-start":
        par_start(a[1], a[2])
    elif a[0] == "par-finish":
        par_finish(a[1], a[2])
    elif a[0] == "step":
        return step(a[1:])
    elif a[0] == "step-key":
        print(step_args(a[1:])[1])
    elif a[0] == "tools":
        print(tools_line())
    elif a[0] == "key-lines":
        # Debugging: the lines a whole step's key is the hash of.
        print("\n".join(base_lines(a[1], a[2])))
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
