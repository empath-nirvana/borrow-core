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
renamed, so a reader sees a whole entry or none. `GATE_CACHE=0` reads and writes nothing;
`GATE_CACHE=record` runs every unit and records its passes (the daily uncached run on main).

    gate_cache.py par-start DIR FN       (scripts/par.sh) keys, hits replayed into DIR, misses printed
    gate_cache.py par-finish DIR FN      store the passing misses, collect side files, print in order
    gate_cache.py step ID CLASS [--files F…] -- CMD…   a whole step, run or replayed
    gate_cache.py step-key ID CLASS [--files F…] -- CMD…   the key `step` would use
    gate_cache.py prune [--days N] [--max-mb M]   remove old entries (never during a gate)
    gate_cache.py tools                  the tools line (ci-local writes it to GATE_CACHE_TOOLS_FILE)
"""
import hashlib, os, re, shutil, subprocess, sys, tempfile

sys.dont_write_bytecode = True
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VERSION = "gate-cache 1"


MODES = ("1", "0", "record")


def mode():
    """`GATE_CACHE`: `1` (the default: replay and record), `0` (neither) or `record` (record, replay
    nothing). Any other value is an error."""
    m = os.environ.get("GATE_CACHE", "1") or "1"
    if m not in MODES:
        sys.stderr.write(f"gate_cache: GATE_CACHE={m}: not one of 1, 0, record\n")
        sys.exit(2)
    return m


def enabled():
    """Whether passes are recorded: `GATE_CACHE` is not `0`."""
    return mode() != "0"


def built(cls):
    """Whether a unit of class cls may use the cache: one that reads the binaries (`bcc`) only once
    they were built in this invocation, by the gate (`CI_LOCAL_BUILT`) or by the script itself
    (`GATE_CACHE_BUILT`, which a script exports after its own build). Stale binaries left by a
    failed build are never looked up."""
    return "bcc" not in cls.split(",") or bool(os.environ.get("CI_LOCAL_BUILT") or os.environ.get("GATE_CACHE_BUILT"))


def reading():
    """Whether recorded passes are replayed: `GATE_CACHE` is neither `0` nor `record`."""
    return mode() == "1"


def store_dir():
    return os.environ.get("GATE_CACHE_DIR") or os.path.join(os.path.expanduser("~"), "repos", ".gate-cache")


_hashes = {}
# Each file's (size, mtime, ctime, inode) when it was hashed, and the files a key computed under
# `recording` read: the recheck after a run compares these too, so a file changed and changed
# back while the unit ran (its content the same, its ctime not) is seen.
_stats = {}
_rec = None


def note_stat(ap):
    if _rec is not None:
        _rec.add(ap)
    if ap not in _stats:
        try:
            st = os.stat(ap)
            _stats[ap] = (st.st_size, st.st_mtime_ns, st.st_ctime_ns, st.st_ino)
        except OSError:
            _stats[ap] = None


def recording(fn):
    """fn's value, and the files and directories it read (through sha_file, listing, tables and
    book_deps, which note each one's stat)."""
    global _rec
    old, _rec = _rec, set()
    try:
        return fn(), _rec
    finally:
        _rec = old


def fingerprint(files):
    return digest([f"{p} {_stats.get(p)}" for p in sorted(files)])


def sha_file(p):
    """The sha256 of file p's bytes, or `absent`."""
    ap = os.path.abspath(p)
    note_stat(ap)
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


def forget():
    """Drop every file hash and listing read so far, to compute a key again."""
    global _tables, _keylines
    _hashes.clear()
    _stats.clear()
    _listings.clear()
    _tables = _keylines = None


def files_lines(tag, paths):
    return [f"{tag} {p} {sha_file(os.path.join(ROOT, p))}" for p in paths]


def tools_line():
    """`uname -sm`, Python, wasmtime and the C compiler `bcc cc` names, with their versions."""
    f = os.environ.get("GATE_CACHE_TOOLS_FILE")
    if f and os.path.isfile(f):
        with open(f) as fh:
            return fh.read().strip()
    import resource
    parts = [" ".join(os.uname()[i] for i in (0, 2, 4)), "python " + sys.version.split()[0],
             "stack " + " ".join(str(x) for x in resource.getrlimit(resource.RLIMIT_STACK))]

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
    m = shutil.which("mdbook")
    parts.append(f"mdbook {m} {out([m, '--version']) if m else '-'}")
    if shutil.which("xcrun"):
        for a in (["--show-sdk-path"], ["--show-sdk-version"], ["ld", "-v"], ["-f", "nm"]):
            parts.append(f"xcrun {' '.join(a)} {out(['xcrun'] + a)}")
    return " | ".join(parts).replace("\n", " ")


ENV_SKIP = {"CI_LOCAL_BUILT", "CI_LOCAL_BASE"}


def env_lines():
    out = []
    for k in sorted(os.environ):
        if (re.match(r"^(BC_|BCC_|CI_LOCAL_|LC_)", k) and k not in ENV_SKIP) or k in ("source_digest", "LANG", "DEVELOPER_DIR", "SDKROOT"):
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


NAMED = re.compile(r'"((?:corpus|lib|book|docs|scripts|research)/[^"{}\s]+)"')


def class_lines(cls, extra=()):
    lines = []
    if "bcc" in cls.split(","):
        # By content only: no path of the worktree enters a key, so every worktree shares entries.
        libs, shas = set(), set()
        for b in binaries(extra):
            shas.add(sha_file(b))
            libs.add(os.path.realpath(lib_of(b)))
        lines += [f"bin {h}" for h in sorted(shas)]
        for l in sorted(libs):
            for r, _, fs in os.walk(l):
                for f in sorted(fs):
                    p = os.path.join(r, f)
                    lines.append(f"lib {os.path.relpath(p, l)} {sha_file(p)}")
    if "lean" in cls.split(","):
        lean = [p for p in walk(".") if p.endswith(".lean")]
        lines += files_lines("lean", lean)
        # A file of the repository a Lean source names in a string (read at elaboration time, as
        # `bcc_program% "corpus/…"` in Frontend/Check/CrossCheck.lean): Lake does not trace it.
        named = set()
        for p in lean:
            with open(os.path.join(ROOT, p), encoding="utf-8", errors="surrogateescape") as fh:
                named.update(NAMED.findall(fh.read()))
        lines += files_lines("named", sorted(f for f in named if os.path.isfile(os.path.join(ROOT, f))))
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
    note_stat(os.path.join(ROOT, d))
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
        note_stat(os.path.join(ROOT, "corpus", t))
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
    note_stat(os.path.join(tmp, "manifest"))
    note_stat(os.path.join(tmp, f"{n}.bc"))
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
    keyfiles = walk("book/keys")
    note_stat(os.path.join(ROOT, "book/keys"))
    for p in keyfiles:
        note_stat(os.path.join(ROOT, p))
    if _keylines is None:
        _keylines = {}
        for p in keyfiles:
            with open(os.path.join(ROOT, p), encoding="utf-8", errors="surrogateescape") as fh:
                for l in fh:
                    _keylines.setdefault(l.split(" ", 1)[0], []).append(l.rstrip("\n"))
    # The job index too: the block's verified keys line is replayed as the side file `ok/<n>`.
    lines = [f"arg {n}", f"block {attrs}\t{md}\t{line}", f"text {hashlib.sha256(text).hexdigest()}"]
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


_put_failed = 0


def put(step, key, out_file, side_dir=None):
    """Record a pass: `out` and `side/` (always present, maybe empty), written under a temporary
    name and renamed. A store that cannot be written is said once per process, loudly."""
    global _put_failed
    final = entry(step, key)
    if os.path.isdir(final):
        if get(final) is not None:
            return
        drop(final)  # not whole (damaged, or from an older version): replaced
    t = None
    try:
        parent = os.path.dirname(final)
        os.makedirs(parent, exist_ok=True)
        t = tempfile.mkdtemp(prefix=".tmp.", dir=parent)
        shutil.copyfile(out_file, os.path.join(t, "out"))
        if side_dir and os.path.isdir(side_dir):
            shutil.copytree(side_dir, os.path.join(t, "side"))
        else:
            os.mkdir(os.path.join(t, "side"))
        with open(os.path.join(t, "sum"), "w") as fh:
            fh.write(entry_sum(t) + "\n")
        os.rename(t, final)
    except OSError as e:
        if t:
            shutil.rmtree(t, ignore_errors=True)
        if os.path.isdir(final):
            return
        if not _put_failed:
            sys.stdout.flush()
            print(f"gate-cache: WARNING: cannot record in {store_dir()} ({e}): passes are not recorded")
            sys.stdout.flush()
        _put_failed += 1


def entry_sum(e):
    """The sha256 over an entry's `out` and every file under its `side/`, each by relative path,
    length and content."""
    h = hashlib.sha256()
    files = ["out"]
    for r, ds, fs in os.walk(os.path.join(e, "side")):
        ds.sort()
        files += sorted(os.path.relpath(os.path.join(r, f), e) for f in fs)
    for f in files:
        with open(os.path.join(e, f), "rb") as fh:
            data = fh.read()
        h.update(f"{f} {len(data)}\n".encode())
        h.update(data)
    return h.hexdigest()


def get(e):
    """An entry's `out` bytes and its `side/` directory, or None when it is not whole and intact:
    no `side/` or no `sum` (being pruned, or written by an older version), or files whose checksum
    is not its `sum` (truncated, say by a power loss before the data reached the disk). Then the
    unit is a miss, and its pass replaces the entry."""
    try:
        with open(os.path.join(e, "out"), "rb") as fh:
            data = fh.read()
        side = os.path.join(e, "side")
        if not os.path.isdir(side):
            return None
        with open(os.path.join(e, "sum")) as fh:
            if fh.read().strip() != entry_sum(e):
                return None
        return data, side
    except OSError:
        return None


def stat(replayed, ran):
    """Add to the gate's counts (`GATE_CACHE_STATS`): units replayed, run, and failed records."""
    s = os.environ.get("GATE_CACHE_STATS")
    if s and (replayed or ran or _put_failed):
        with open(s, "a") as fh:
            fh.write(f"{replayed} {ran} {_put_failed}\n")


# --- par --------------------------------------------------------------------------------------

def read_jobs(d):
    with open(os.path.join(d, "jobs"), encoding="utf-8", errors="surrogateescape") as fh:
        ws = fh.read().split("\n")
    return [(ws[k], ws[k + 1]) for k in range(0, len(ws) - 1, 2)]


def weight_file(step, arg):
    """Where a unit's memory weight is kept: by step and argument, not by key, so a unit that
    misses (its key changed) still finds the peak its last run reached."""
    return os.path.join(store_dir(), re.sub(r"[^A-Za-z0-9_.-]+", "_", step), "weights",
                        hashlib.sha256(arg.encode("utf-8", "surrogateescape")).hexdigest()[:32])


def weight(step, arg):
    """The memory tokens (GB) a unit's job takes in the job pool (scripts/slot): the peak resident
    memory its last run reached (scripts/par_unit.py records it), rounded up, or `$PAR_MEM` (default
    1) when it has not run. Not a part of any key: it decides only when the job starts."""
    try:
        with open(weight_file(step, arg)) as fh:
            return max(1, int(fh.read().split()[0]))
    except (OSError, ValueError, IndexError):
        return int(os.environ.get("PAR_MEM", "1"))


class ParKeys:
    """The keys of one `par` call's units, and the fingerprint (`fingerprint`) of the files each
    read: the base once, then each unit's own files."""

    def __init__(self, fn):
        self.spec = os.environ.get("PAR_CACHE", "")
        self.mode = os.environ.get("PAR_CACHE_DEPS", "corpus")
        self.step = self.spec.split()[0]
        self.base, self.base_files = recording(
            lambda: base_lines(self.spec, "bcc") + [f"fn {fn}", f"deps {self.mode}"])

    def of(self, arg):
        deps, files = recording(lambda: unit_deps(self.mode, arg))
        self.files = files
        return digest(self.base + deps), fingerprint(self.base_files | files)


def par_start(d, fn):
    """Read DIR/jobs (`i` and `arg`, a line each); for each hit, write DIR/i.out, DIR/i.rc and
    DIR/i.side as the run would have; print the misses (`i` and `arg`, a line each) for xargs."""
    jobs = read_jobs(d)
    if not os.environ.get("PAR_CACHE") or not enabled() or not built("bcc"):
        for i, a in jobs:
            sys.stdout.write(f"{i}\n{a}\n")
        return
    tools = tools_line()
    with open(os.path.join(d, "tools"), "w") as fh:
        fh.write(tools)
    os.environ["GATE_CACHE_TOOLS_FILE"] = os.path.join(d, "tools")
    pk = ParKeys(fn)
    keys, misses = [], []
    for i, a in jobs:
        k, fp = pk.of(a)
        keys.append(f"{i} {k} {fp}")
        got = get(entry(pk.step, k)) if reading() else None
        if got:
            data, side = got
            try:
                shutil.copytree(side, os.path.join(d, f"{i}.side"), dirs_exist_ok=True)
                with open(os.path.join(d, f"{i}.out"), "wb") as fh:
                    fh.write(data)
                with open(os.path.join(d, f"{i}.rc"), "w") as fh:
                    fh.write("0\n")
                with open(os.path.join(d, f"{i}.hit"), "w"):
                    pass
                try:
                    os.utime(entry(pk.step, k))
                except OSError:
                    pass
                continue
            except OSError:
                for x in (f"{i}.out", f"{i}.rc", f"{i}.hit"):
                    try:
                        os.remove(os.path.join(d, x))
                    except OSError:
                        pass
                shutil.rmtree(os.path.join(d, f"{i}.side"), ignore_errors=True)
        sys.stdout.write(f"{i}\n{a}\n")
        misses.append(i)
        with open(os.path.join(d, f"{i}.files"), "w", encoding="utf-8", errors="surrogateescape") as fh:
            fh.write("".join(f"{p}\n" for p in sorted(pk.files)))
    with open(os.path.join(d, "keys"), "w") as fh:
        fh.write("\n".join(keys) + "\n")
    # For scripts/par_unit.py, which runs each miss so that a gate missing the same key at the same
    # time waits on the entry's lock and replays it, and stores a pass as soon as its job ends: the
    # files the base read (each miss's own are DIR/i.files), and each miss's memory weight.
    with open(os.path.join(d, "base.files"), "w", encoding="utf-8", errors="surrogateescape") as fh:
        fh.write("".join(f"{p}\n" for p in sorted(pk.base_files)))
    with open(os.path.join(d, "entries"), "w", encoding="utf-8", errors="surrogateescape") as fh:
        args = dict(jobs)
        fh.write("".join(f"{i} {weight(pk.step, args[i])}\n" for i in misses))


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
    """Store each miss that passed, did not mark itself `nostore`, and whose key and fingerprint,
    computed again now, are those it ran under (no input changed while it ran, even and back);
    append each job's side files to $PAR_COLLECT in job order; print each job's output in order;
    write the number of jobs that failed to DIR/failed."""
    jobs = read_jobs(d)
    keys = {}
    kp = os.path.join(d, "keys")
    if os.path.exists(kp):
        for l in open(kp):
            w = l.split()
            if len(w) == 3:
                keys[w[0]] = (w[1], w[2])
    collect = os.environ.get("PAR_COLLECT", "")
    failed = replayed = ran = 0
    pk = None
    out = sys.stdout.buffer
    for j, (i, a) in enumerate(jobs, 1):
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
                if rc == "0" and i in keys and not os.path.exists(os.path.join(d, f"{i}.nostore")) \
                        and not os.path.exists(os.path.join(d, f"{i}.stored")):
                    if pk is None:
                        os.environ["GATE_CACHE_TOOLS_FILE"] = os.path.join(d, "tools")
                        pk = ParKeys(fn)
                    if pk.of(a) == keys[i]:
                        put(pk.step, keys[i][0], o, side)
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
    """`ID CLASS [--files F…] -- CMD…`: the step's id, its key and fingerprint, and CMD."""
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
    if not enabled() or not built(cls):
        return sid, None, None, cmd

    def lines():
        paths = []
        for f in files:
            if os.path.isdir(os.path.join(ROOT, f)):
                paths += walk(f)
            else:
                paths.append(f)
        return base_lines(sid, cls) + [f"cmd {' '.join(cmd)}"] + files_lines("file", sorted(set(paths)))
    ls, read = recording(lines)
    return sid, digest(ls), fingerprint(read), cmd


def step(argv):
    """`step ID CLASS [--files F…] -- CMD…`: the step's recorded pass, or CMD run (with
    GATE_CACHE_INNER=ID, so a script that wraps itself runs its body) and its pass recorded. The
    key covers the class's inputs (`bcc`: the binaries and the library; `lean`: the Lean sources
    and the Lake configuration), scripts/, the tools, the environment, CMD and the files (or every
    file under the directories) named."""
    sid, key, fp, cmd = step_args(argv)
    env = dict(os.environ, GATE_CACHE_INNER=sid)
    if key is None:
        os.chdir(ROOT)
        os.execvpe(cmd[0], cmd, env)
    e = entry(sid, key)
    got = get(e) if reading() else None
    if got:
        try:
            os.utime(e)
        except OSError:
            pass
        sys.stdout.buffer.write(got[0])
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
        if rc == 0 and not os.path.exists(env["GATE_CACHE_NOSTORE"]):
            forget()
            if step_args(argv)[1:3] == (key, fp):
                put(sid, key, log)
        stat(0, 1)
        return rc
    finally:
        shutil.rmtree(t, ignore_errors=True)


def wrap_self(sid, cls, files=()):
    """For a Python script: run the rest of the script under `step`, unless already inside it."""
    if os.environ.get("GATE_CACHE_INNER") == sid or not enabled() or not built(cls):
        return
    script = os.path.relpath(os.path.abspath(sys.argv[0]), ROOT)
    argv = [sid, cls] + (["--files", *files] if files else []) + ["--", "python3", script, *sys.argv[1:]]
    sys.stdout.flush()
    sys.exit(step(argv))


# --- for a script that keeps its own units (scripts/alpha-check.py) ---------------------------

class Units:
    """Keys of one step's units, computed with the same base as `par`."""

    def __init__(self, spec, mode="corpus", cls="bcc", bins=()):
        self.on = enabled() and built(cls)
        self.step = spec.split()[0]
        self.args = (spec, cls, bins, mode)
        self.mode = mode
        self.replayed = self.ran = 0
        self.passed = []
        if self.on:
            self.base, self.base_files = recording(lambda: base_lines(spec, cls, bins) + [f"deps {mode}"])

    def key(self, arg):
        """The unit's key and fingerprint, or None when the cache is off."""
        if not self.on:
            return None
        deps, files = recording(lambda: unit_deps(self.mode, arg))
        return digest(self.base + deps), fingerprint(self.base_files | files)

    def hit(self, key):
        return self.on and reading() and key is not None and get(entry(self.step, key[0])) is not None

    def pass_(self, arg, key, text=""):
        if self.on and key is not None:
            self.passed.append((arg, key, text))

    def done(self):
        """Record the passes whose key and fingerprint, computed again now, are those they ran
        under."""
        if not self.on:
            return
        if self.passed:
            forget()
            spec, cls, bins, mode = self.args
            self.base, self.base_files = recording(lambda: base_lines(spec, cls, bins) + [f"deps {mode}"])
            t = tempfile.mkdtemp(prefix="gate-cache-")
            try:
                for arg, key, text in self.passed:
                    if self.key(arg) != key:
                        continue
                    o = os.path.join(t, "out")
                    with open(o, "w") as fh:
                        fh.write(text)
                    put(self.step, key[0], o)
            finally:
                shutil.rmtree(t, ignore_errors=True)
        stat(self.replayed, self.ran)


def drop(p):
    """Remove entry p: renamed to a temporary name first (atomic), so a gate reading it sees the
    whole entry or none (a miss), never a part."""
    if not os.path.basename(p).startswith(".tmp."):
        t = os.path.join(os.path.dirname(p), ".tmp.prune." + os.path.basename(p))
        try:
            os.rename(p, t)
        except OSError:
            return
        p = t
    shutil.rmtree(p, ignore_errors=True)


def prune(argv):
    """`prune [--days N] [--max-mb M]`: remove the entries not used for N days (default 14), then
    the least recently used until the store holds at most M MiB. An entry's time is its directory's
    modification time, which a replay renews (`touch`). Never run during a gate."""
    days, maxmb = 14.0, None
    k = 0
    while k < len(argv):
        if argv[k] == "--days":
            days = float(argv[k + 1]); k += 2
        elif argv[k] == "--max-mb":
            maxmb = float(argv[k + 1]); k += 2
        else:
            raise SystemExit("usage: gate_cache.py prune [--days N] [--max-mb M]")
    import time
    root = store_dir()
    entries = []
    for st in (os.listdir(root) if os.path.isdir(root) else []):
        sd = os.path.join(root, st)
        if not os.path.isdir(sd):
            continue
        for e in os.listdir(sd):
            p = os.path.join(sd, e)
            if e.endswith(".lock"):
                continue
            size = 0
            for r, _, fs in os.walk(p):
                for f in fs:
                    try:
                        size += os.lstat(os.path.join(r, f)).st_size
                    except OSError:
                        pass
            entries.append((os.stat(p).st_mtime, size, p))
    now = time.time()
    removed = freed = 0
    keep = []
    for m, size, p in entries:
        tmp = os.path.basename(p).startswith(".tmp.")
        # A temporary entry an hour old is left over from an interrupted write; a younger one may
        # be another gate's write in progress.
        if now - m > (3600 if tmp else days * 86400):
            drop(p); removed += 1; freed += size
        else:
            keep.append((m, size, p))
    total = sum(sz for _, sz, _ in keep)
    if maxmb is not None:
        for m, size, p in sorted(keep):
            if total <= maxmb * 1048576:
                break
            if os.path.basename(p).startswith(".tmp."):
                continue
            drop(p); removed += 1; freed += size; total -= size
    # An entry's lock (scripts/par_unit.py) goes with its entry, or after an hour if it has none.
    for st in (os.listdir(root) if os.path.isdir(root) else []):
        sd = os.path.join(root, st)
        if not os.path.isdir(sd):
            continue
        for e in os.listdir(sd):
            p = os.path.join(sd, e)
            if e.endswith(".lock") and not os.path.isdir(p[: -len(".lock")]):
                try:
                    if now - os.stat(p).st_mtime > 3600:
                        os.remove(p)
                except OSError:
                    pass
    print(f"gate_cache: removed {removed} entr{'y' if removed == 1 else 'ies'} ({freed / 1048576:.1f} MiB); {total / 1048576:.1f} MiB left in {root}")


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
    elif a[0] == "unit-key":
        # The key of one `par` unit: `unit-key FN ARG`, with PAR_CACHE and PAR_CACHE_DEPS set.
        spec, m = os.environ["PAR_CACHE"], os.environ.get("PAR_CACHE_DEPS", "corpus")
        print(digest(base_lines(spec, "bcc") + [f"fn {a[1]}", f"deps {m}"] + unit_deps(m, a[2])))
    elif a[0] == "step-key":
        print(step_args(a[1:])[1])
    elif a[0] == "prune":
        prune(a[1:])
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
