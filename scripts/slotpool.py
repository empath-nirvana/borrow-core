"""The machine-wide job pool (scripts/slot) for the gate's Python thread pools.

`with held(mem=1): subprocess.run(…)` runs its body holding one CPU slot and MEM memory tokens of
the pool, taken by the same protocol as scripts/slot (the door, then `cpu.<i>` and `mem.<i>` by
non-blocking flock): a thread pool's width then bounds only how many subprocesses wait, and the
pool bounds how many run, machine-wide. The locks are this process's: the kernel drops them when
it exits, however it exits. A subprocess's own timeout counts from when it starts, as before.

The pool is off (the body runs at once) with `SLOT_OFF=1`, inside a slot already (`SLOT_HELD`),
or when scripts/slot does not answer (`slot -s`), as ci-local and scripts/par.sh decide.
"""
import contextlib, fcntl, os, random, subprocess, time

SLOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "slot")
DIR = os.environ.get("SLOT_DIR") or os.path.join(os.path.expanduser("~"), "repos", ".gate-slots")


def _size():
    """The pool's size `(N, M)` (scripts/slot writes it on first use), or None when it is off."""
    if os.environ.get("SLOT_OFF") == "1" or os.environ.get("SLOT_HELD"):
        return None
    try:
        n, m = subprocess.run([SLOT, "-s"], capture_output=True, text=True, check=True).stdout.split()
        return int(n), int(m)
    except (OSError, subprocess.CalledProcessError, ValueError):
        return None


SIZE = _size()


@contextlib.contextmanager
def held(mem=1):
    if SIZE is None:
        yield
        return
    n, m = SIZE
    fds = []
    door = os.open(os.path.join(DIR, "door"), os.O_RDWR | os.O_CREAT)
    try:
        fcntl.flock(door, fcntl.LOCK_EX)
        for name, total, want in (("cpu", n, 1), ("mem", m, min(mem, m))):
            got, start, sleep = 0, random.randrange(total), 0.002
            while got < want:
                for k in range(total):
                    if got >= want:
                        break
                    fd = os.open(os.path.join(DIR, f"{name}.{(start + k) % total}"), os.O_RDWR | os.O_CREAT)
                    try:
                        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        fds.append(fd)
                        got += 1
                    except BlockingIOError:
                        os.close(fd)
                if got < want:
                    time.sleep(sleep)
                    sleep = min(sleep * 2, 0.05)
    finally:
        os.close(door)
    try:
        yield
    finally:
        for fd in fds:
            os.close(fd)
