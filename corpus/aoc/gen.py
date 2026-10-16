#!/usr/bin/env python3
# Inputs for the Advent of Code ports (corpus/aoc/): each has the structure of its puzzle's input,
# generated from a fixed seed, so `python3 corpus/aoc/gen.py <yyyy-dd>` writes the same
# `<yyyy-dd>.in` every time. The expected answers come from running the Rust solution on it.
import random
import sys


def d2022_01(r):
    groups = []
    for _ in range(40):
        groups.append("\n".join(str(r.randint(1000, 60000)) for _ in range(r.randint(1, 6))))
    return "\n\n".join(groups) + "\n"


def d2023_01(r):
    names = ["one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]
    lines = []
    for _ in range(60):
        parts = [str(r.randint(1, 9))]
        for _ in range(r.randint(1, 5)):
            k = r.random()
            if k < 0.3:
                parts.append(r.choice(names))
            elif k < 0.5:
                parts.append(str(r.randint(1, 9)))
            else:
                parts.append("".join(r.choice("abcdefghijklmnopqrstuvwxyz") for _ in range(r.randint(1, 4))))
        r.shuffle(parts)
        lines.append("".join(parts))
    return "\n".join(lines) + "\n"


def d2024_02(r):
    lines = []
    for _ in range(60):
        n = r.randint(5, 8)
        step = r.choice([-1, 1])
        xs = [r.randint(10, 90)]
        for _ in range(n - 1):
            xs.append(xs[-1] + step * r.randint(1, 3))
        k = r.random()
        if k < 0.35:
            xs[r.randrange(n)] += r.choice([-5, -2, 0, 3, 6])
        elif k < 0.6:
            xs[r.randrange(n)] += r.randint(-9, 9)
            xs[r.randrange(n)] += r.randint(-9, 9)
        lines.append(" ".join(map(str, xs)))
    return "\n".join(lines) + "\n"


def d2021_10(r):
    pairs = {"(": ")", "[": "]", "{": "}", "<": ">"}
    lines = []
    for _ in range(50):
        out, stack = [], []
        for _ in range(r.randint(30, 70)):
            if stack and (len(stack) >= 24 or r.random() < 0.35):
                out.append(pairs[stack.pop()])
            else:
                c = r.choice("([{<")
                stack.append(c)
                out.append(c)
        if r.random() < 0.5:
            closers = [i for i, c in enumerate(out) if c in ")]}>"]
            if closers:
                i = r.choice(closers)
                out[i] = r.choice([c for c in ")]}>" if c != out[i]])
        lines.append("".join(out))
    return "\n".join(lines) + "\n"


def d2021_06(r):
    return ",".join(str(r.randint(1, 5)) for _ in range(300)) + "\n"


def d2020_08(r):
    def run(prog):
        pc, acc, seen = 0, 0, set()
        while 0 <= pc < len(prog) and pc not in seen:
            seen.add(pc)
            op, x = prog[pc]
            if op == "acc":
                acc += x
            pc += x if op == "jmp" else 1
        return pc == len(prog)

    flip = {"jmp": "nop", "nop": "jmp", "acc": "acc"}
    while True:
        prog = []
        for _ in range(150):
            op = r.choices(["acc", "jmp", "nop"], [5, 3, 2])[0]
            x = r.randint(-50, 50) if op == "acc" else r.choice([-1, 1]) * r.randint(1, 20)
            prog.append((op, x))
        if run(prog):
            continue
        fixes = [i for i, (op, x) in enumerate(prog)
                 if op != "acc" and run(prog[:i] + [(flip[op], x)] + prog[i + 1:])]
        if len(fixes) == 1:
            return "".join(f"{op} {x:+d}\n" for op, x in prog)


def d2022_12(r):
    w, h = 40, 20
    while True:
        ex, ey = r.randrange(w // 2, w), r.randrange(h)
        rows = []
        for y in range(h):
            row = []
            for x in range(w):
                d = abs(x - ex) + abs(y - ey)
                v = max(0, min(25, 25 - d // 2 + r.randint(-2, 1)))
                row.append(chr(97 + v))
            rows.append(row)
        rows[ey][ex] = "E"
        sy = r.randrange(h)
        rows[sy][0] = "S"
        hgt = lambda c: 0 if c == "S" else 25 if c == "E" else ord(c) - 97
        seen, todo, ok = {(ex, ey)}, [(ex, ey)], False
        while todo:
            x, y = todo.pop()
            if rows[y][x] == "S":
                ok = True
            for nx, ny in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
                if 0 <= nx < w and 0 <= ny < h and (nx, ny) not in seen \
                        and hgt(rows[y][x]) - hgt(rows[ny][nx]) <= 1:
                    seen.add((nx, ny))
                    todo.append((nx, ny))
        if ok:
            return "".join("".join(row) + "\n" for row in rows)


def d2021_15(r):
    return "".join("".join(str(r.randint(1, 9)) for _ in range(10)) + "\n" for _ in range(10))


def d2023_07(r):
    hands = set()
    while len(hands) < 100:
        pool = r.sample("AKQJT98765432", r.randint(1, 5))
        hands.add("".join(r.choice(pool) for _ in range(5)))
    hands = sorted(hands)
    r.shuffle(hands)
    return "".join(f"{h} {r.randint(1, 999)}\n" for h in hands)


def d2023_03(r):
    w = h = 30
    rows = [["."] * w for _ in range(h)]
    for y in range(h):
        x = r.randint(0, 3)
        while x < w - 1:
            n = str(r.randint(1, 999))
            if x + len(n) <= w:
                rows[y][x:x + len(n)] = list(n)
            x += len(n) + r.randint(1, 6)
    for _ in range(70):
        x, y = r.randint(1, w - 2), r.randint(1, h - 2)
        if rows[y][x] == ".":
            rows[y][x] = r.choice("**#+$/@=%-&")
    return "".join("".join(row) + "\n" for row in rows)


def d2024_01(r):
    left = [r.randint(10000, 99999) for _ in range(200)]
    pool = left[:60] + [r.randint(10000, 99999) for _ in range(40)]
    right = [r.choice(pool) for _ in range(200)]
    return "".join(f"{a}   {b}\n" for a, b in zip(left, right))


def d2024_11(r):
    return " ".join(str(r.randint(0, 999999)) for _ in range(8)) + "\n"


def d2022_21(r):
    names = set()

    def fresh():
        while True:
            n = "".join(r.choice("abcdefghijklmnopqrstuvwxyz") for _ in range(4))
            if n not in names and n not in ("root", "humn"):
                names.add(n)
                return n

    lines = {}

    def known(depth):
        # A subtree without `humn`: its name and value; a division only where it is exact.
        n = fresh()
        if depth == 0 or r.random() < 0.25:
            v = r.randint(1, 20)
            lines[n] = str(v)
            return n, v
        (a, x), (b, y) = known(depth - 1), known(depth - 1)
        op = r.choice("+-*/" if y != 0 and x % y == 0 else "+-*")
        v = {"+": x + y, "-": x - y, "*": x * y, "/": x // y if y else 0}[op]
        if op == "*" and abs(v) > 10 ** 9:
            op, v = "+", x + y
        lines[n] = f"{a} {op} {b}"
        return n, v

    def unknown(depth):
        # The path down to `humn`, as a function of what `humn` yells.
        if depth == 0:
            lines["humn"] = str(r.randint(1, 20))
            return "humn", lambda h: h
        sub, f = unknown(depth - 1)
        k, y = known(2)
        op = r.choice("+-**")
        n = fresh()
        if r.random() < 0.5:
            lines[n] = f"{sub} {op} {k}"
            g = {"+": lambda h: f(h) + y, "-": lambda h: f(h) - y, "*": lambda h: f(h) * y}[op]
        else:
            lines[n] = f"{k} {op} {sub}"
            g = {"+": lambda h: y + f(h), "-": lambda h: y - f(h), "*": lambda h: y * f(h)}[op]
        return n, g

    def literal(v):
        # A subtree that yells exactly `v`, from leaves 1 to 10: its digits by Horner's rule.
        if v < 1:
            one, rest = fresh(), literal(1 - v)
            lines[one] = "1"
            n = fresh()
            lines[n] = f"{one} - {rest}"
            return n
        acc = None
        for d in str(v):
            leaf = fresh()
            lines[leaf] = d if d != "0" else "10"
            if acc is None:
                acc = leaf
                if d == "0":
                    acc = fresh()
                    lines[acc] = f"{leaf} - {leaf}"
                continue
            ten, times, n = fresh(), fresh(), fresh()
            lines[ten] = "10"
            lines[times] = f"{acc} * {ten}"
            lines[n] = f"{times} + {leaf}" if d != "0" else f"{times} + {fresh_zero()}"
            acc = n
        return acc

    def fresh_zero():
        a, n = fresh(), fresh()
        lines[a] = "7"
        lines[n] = f"{a} - {a}"
        return n

    side, f = unknown(16)
    top = literal(f(r.randint(100, 999)))
    lines["root"] = f"{side} + {top}" if r.random() < 0.5 else f"{top} + {side}"
    order = list(lines)
    r.shuffle(order)
    return "".join(f"{n}: {lines[n]}\n" for n in order)


def d2020_07(r):
    # The Rust names a colour by a perfect hash of these words, so the colours are made of them.
    adjectives = ("bright clear dark dim dotted drab dull faded light mirrored muted pale plaid posh"
                  " shiny striped vibrant wavy").split()
    colours = ("aqua beige black blue bronze brown chartreuse coral crimson cyan fuchsia gold gray"
               " green indigo lavender lime magenta maroon olive orange plum purple red salmon"
               " silver tan teal tomato turquoise violet white yellow").split()
    names = [f"{a} {c}" for a in adjectives for c in colours if f"{a} {c}" != "shiny gold"]
    bags = r.sample(names, 99)
    bags.insert(50, "shiny gold")
    lines = []
    for i, bag in enumerate(bags):
        inner = r.sample(bags[i + 1:], min(len(bags) - i - 1, r.randint(0, 4))) if i < 95 else []
        if inner and r.random() < 0.15:
            inner = []
        if i < 50 and "shiny gold" not in inner and r.random() < 0.12:
            inner = inner[:3] + ["shiny gold"]
        if inner:
            parts = []
            for b in inner:
                n = r.randint(1, 4)
                parts.append(f"{n} {b} bag{'s' if n > 1 else ''}")
            lines.append(f"{bag} bags contain {', '.join(parts)}.")
        else:
            lines.append(f"{bag} bags contain no other bags.")
    r.shuffle(lines)
    return "\n".join(lines) + "\n"


DAYS = {"2020-07": d2020_07, "2022-21": d2022_21, "2024-11": d2024_11, "2024-01": d2024_01, "2023-03": d2023_03, "2023-07": d2023_07, "2021-15": d2021_15, "2022-12": d2022_12, "2020-08": d2020_08, "2021-06": d2021_06, "2021-10": d2021_10, "2024-02": d2024_02, "2022-01": d2022_01, "2023-01": d2023_01}

if __name__ == "__main__":
    for name in sys.argv[1:]:
        text = DAYS[name](random.Random(name))
        with open(f"{sys.path[0]}/{name}.in", "w") as f:
            f.write(text)
