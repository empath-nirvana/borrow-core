"""One miss of a cached `par` call (scripts/par.sh), run so that two gates share it.

    python3 scripts/par_unit.py DIR -- CMD… I ARG     (xargs appends job I's index and argument)

CMD I ARG is the job. When DIR/entries lists job I (scripts/gate_cache.py `par-start`: a miss of
a cached call), the job holds its entry's lock, `<entry>.lock` (flock, so the kernel drops it
when this process exits, however it exits), from before it starts until its pass is stored:

  * a gate that misses the same key meanwhile waits on the lock, then finds the entry whole
    (`gate_cache.get`) and replays it (its output, side files and status 0, as `par-start` replays
    a hit), instead of running the job again;
  * the job's pass is stored (`gate_cache.put`) as soon as it ends, if the job passed, did not
    mark itself `nostore`, and the fingerprint of every file and directory its key read
    (DIR/base.files and DIR/I.files), taken now, is the one `par-start` took before reading them:
    par_finish's recheck, made per job. par_finish skips the jobs stored here (DIR/I.stored).

Why the fingerprint at job end is at least as strong as hashing the inputs again: any write to a
file's contents advances its ctime (the kernel sets it; no system call sets it back, unlike
mtime), a file replaced by rename has another inode, and an entry added or removed advances its
directory's ctime; every file and directory a key reads has its stat noted before it is read. So
equal fingerprints mean no input was written between the key's read and the job's end: the job read
what the key hashed. A rehash shows only that the end state equals the hashed one, and misses a
change made and undone while the job ran.

The job takes its slot of the job pool after the lock (CMD starts with scripts/slot), so a job
waiting on another gate's unit holds no slot. Locks are taken only by jobs that start, so a
waiting job waits only on a running one. The job's peak memory is recorded as the unit's weight
for its next miss (`gate_cache.weight`).
"""
import fcntl, hashlib, math, os, resource, shutil, subprocess, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gate_cache as gc  # noqa: E402


def lines(p):
    with open(p, encoding="utf-8", errors="surrogateescape") as fh:
        return [l.rstrip("\n") for l in fh if l.strip()]


def replay(d, i, got, e):
    data, side = got
    shutil.copytree(side, os.path.join(d, f"{i}.side"), dirs_exist_ok=True)
    with open(os.path.join(d, f"{i}.out"), "wb") as fh:
        fh.write(data)
    with open(os.path.join(d, f"{i}.rc"), "w") as fh:
        fh.write("0\n")
    open(os.path.join(d, f"{i}.hit"), "w").close()
    try:
        os.utime(e)
    except OSError:
        pass


def record_weight(step, arg):
    """The job's peak resident memory (its largest process), in whole GB rounded up."""
    peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    if sys.platform != "darwin":
        peak *= 1024  # Linux reports KiB
    f = gc.weight_file(step, arg)
    try:
        os.makedirs(os.path.dirname(f), exist_ok=True)
        t = f"{f}.tmp.{os.getpid()}"
        with open(t, "w") as fh:
            fh.write(f"{max(1, math.ceil(peak / 2**30))}\n")
        os.replace(t, f)
    except OSError:
        pass


def main():
    d = sys.argv[1]
    if sys.argv[2] != "--" or len(sys.argv) < 6:
        sys.exit("usage: par_unit.py DIR -- CMD… I ARG")
    cmd = sys.argv[3:]
    i, arg = cmd[-2], cmd[-1]
    weights = dict(l.split(" ", 1) for l in lines(os.path.join(d, "entries")))
    if i not in weights:
        os.execvp(cmd[0], cmd)
    keys = {w[0]: (w[1], w[2]) for w in (l.split() for l in lines(os.path.join(d, "keys"))) if len(w) == 3}
    key, fp = keys[i]
    step = os.environ["PAR_CACHE"].split()[0]
    e = gc.entry(step, key)
    # The job's memory tokens in the pool: the unit's learned weight (gate_cache.weight).
    # UNPROVED: a unit's peak memory is near its last run's. A unit that has never run takes the
    # default (1 GB); one far above it (json-parse.bc's check, 3.6 GB) can overshoot the pool's
    # memory bound once, until its peak is recorded. What breaks then is memory pressure (swap)
    # beside other gates, never a verdict; the pool keeps 1/4 of the RAM outside its bound.
    if len(cmd) > 3 and cmd[1] == "-m" and os.path.basename(cmd[0]) == "slot":
        cmd[2] = weights[i]
    os.makedirs(os.path.dirname(e), exist_ok=True)
    lock = os.open(e + ".lock", os.O_RDWR | os.O_CREAT)
    fcntl.flock(lock, fcntl.LOCK_EX)
    if gc.reading():
        got = gc.get(e)
        if got is not None:
            try:
                replay(d, i, got, e)
                return 0
            except OSError:
                for x in (f"{i}.out", f"{i}.rc", f"{i}.hit"):
                    try:
                        os.remove(os.path.join(d, x))
                    except OSError:
                        pass
                shutil.rmtree(os.path.join(d, f"{i}.side"), ignore_errors=True)
    rc = subprocess.call(cmd)
    record_weight(step, arg)
    try:
        ok = open(os.path.join(d, f"{i}.rc")).read().strip() == "0"
    except OSError:
        ok = False
    if ok and not os.path.exists(os.path.join(d, f"{i}.nostore")):
        files = set(lines(os.path.join(d, "base.files"))) | set(lines(os.path.join(d, f"{i}.files")))
        for p in files:
            gc.note_stat(p)
        if gc.fingerprint(files) == fp:
            gc.put(step, key, os.path.join(d, f"{i}.out"), os.path.join(d, f"{i}.side"))
            if gc.get(e) is not None:
                open(os.path.join(d, f"{i}.stored"), "w").close()
            gc.stat(0, 0)
    return rc


sys.exit(main())
