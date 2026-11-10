"""`python3 -I jsoncmp.py A B`: whether the JSON documents in files `A` and `B` are the same value,
for `check.sh`. Python's reader is the oracle: it reads every float correctly rounded and every
integer exactly (serde_json's default float reader is not correctly rounded, so it cannot judge).

Objects compare as maps (member order is not compared; a key given twice keeps its last value),
arrays element by element, strings by their decoded text. Two integers compare exactly; any other
pair of numbers compares as `float`, so `1e3`, `1000` and `1000.0` are equal, an integer past
`i64` equals the float it rounds to, and `-0` equals `0`. Exit 0 when equal; else 1, with the
number of differences and the first five, by path, on standard error. A file that does not parse
is exit 2.
"""

import json
import sys


def num_eq(a, b):
    if isinstance(a, int) and isinstance(b, int):
        return a == b
    return float(a) == float(b)


def diff(a, b, path, out):
    num = (int, float)
    if isinstance(a, bool) or isinstance(b, bool):
        if a is not b:
            out.append(f"{path}: {short(a)} vs {short(b)}")
    elif isinstance(a, num) and isinstance(b, num):
        if not num_eq(a, b):
            out.append(f"{path}: {short(a)} vs {short(b)}")
    elif isinstance(a, list) and isinstance(b, list) and len(a) == len(b):
        for i, (u, v) in enumerate(zip(a, b)):
            diff(u, v, f"{path}[{i}]", out)
    elif isinstance(a, dict) and isinstance(b, dict) and len(a) == len(b):
        for k, u in a.items():
            if k not in b:
                out.append(f"{path}.{json.dumps(k)}: missing on the right")
            else:
                diff(u, b[k], f"{path}.{json.dumps(k)}", out)
    elif type(a) is not type(b) or a != b:
        out.append(f"{path}: {short(a)} vs {short(b)}")


def short(v):
    s = json.dumps(v, ensure_ascii=False)
    return s if len(s) <= 80 else s[:80] + "…"


def load(f):
    with open(f, "rb") as h:
        return json.loads(h.read())


def main():
    if len(sys.argv) != 3:
        print("usage: jsoncmp.py A B", file=sys.stderr)
        return 2
    try:
        a, b = load(sys.argv[1]), load(sys.argv[2])
    except (OSError, ValueError) as e:
        print(f"jsoncmp: {e}", file=sys.stderr)
        return 2
    out = []
    sys.setrecursionlimit(100000)
    diff(a, b, "$", out)
    if not out:
        return 0
    print(f"jsoncmp: {len(out)} difference(s); the first:", file=sys.stderr)
    for d in out[:5]:
        print(f"  {d}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
