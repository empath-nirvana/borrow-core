#!/usr/bin/env python3
"""The combination check of `let mut` (SPEC §41, #611, #613).

Random nestings of the constructs below, each assigning the outer `let mut`s `a` and `b`, with
binders named as `a` and `b` at every binding position. Each program is written once with
`let mut` and run by `bcc interp`, and its answer is compared with two oracles:

* the answer this script computes by evaluating the program itself (`Eval`): lexical scope, and
  an assignment updating the variable it names wherever the assignment is, the meaning SPEC §41
  gives every construct;
* where the constructs allow it (`STATE_OK`), the same program with `a` and `b` as instances of
  the ordinary control effect `State` (`ha.get()`, `ha.put(v)`), which the kernel runs as handlers
  (#611).

`agree` counts the programs whose answer every applicable oracle gives; `differ` a wrong answer;
`refused` a `let mut` program `bcc` refuses, listed by message. The gate (`--gate`) runs `ROWS`
and fails on any difference or refusal.

    scripts/mut-combos.py [--seed N] [--count N] [--depth N] [--keep DIR] [--jobs N] [--bcc BCC]
                          [--constructs a,b,…] [--without a,b,…] [--gate]
"""
import argparse, os, random, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

HEAD = '''effect State[T] { linear ctl get() -> T; linear ctl put(v: T) }

handler state[T, A](mut s: T): State[T], A -> A * T = {
  return(a) = (a, s);
  get(k) = k(s);
  put(v, k) = { s = v; k(()) }
}

effect Pause { ctl pause() }

handler resuming[A]: Pause, A -> A = { return(a) = a; pause(k) = k(()) }

fn ap(f: !(i32 => i32)) -> i32 = f(1) * 10 + f(2)

fn bump(x: i32) -> i32 * i32 = (x + 1, x)
'''

GEN_HEAD = '''include yield

fn upto(n: i32) -> 1 with Yield[i32] =
  let mut i = 0;
  while i < n { yield(i); i = i + 1 }
'''

# The constructs, the statements among them, those that nest, and those the State form expresses.
ALL = ['assign', 'bindassign', 'rebind', 'shadow', 'pause', 'if', 'lethead', 'match', 'for',
       'block', 'while', 'modify', 'borrow', 'with', 'gen', 'run']
STATEMENTS = ['assign', 'bindassign', 'rebind', 'shadow', 'pause']
NESTING = ['if', 'lethead', 'match', 'for', 'block', 'while', 'modify', 'borrow', 'with', 'gen',
           'run']
STATE_OK = {'assign', 'bindassign', 'rebind', 'shadow', 'pause', 'if', 'lethead', 'match', 'for',
            'block', 'with', 'run'}

# The gate's rows: each a set of constructs, nested to `--depth`.
ROWS = [
    ('joins', ['assign', 'bindassign', 'rebind', 'shadow', 'pause', 'if', 'lethead', 'match',
               'for']),
]

M32 = 0xffffffff


def wrap(x):
    x &= M32
    return x - (1 << 32) if x >= 1 << 31 else x


class Gen:
    """A program as a tree. A scope maps each name to whether it is one of the outer `let mut`s;
    `muts` are those still assignable (not shadowed)."""

    def __init__(self, rng, depth, constructs):
        self.rng, self.depth, self.n = rng, depth, 0
        self.constructs = constructs
        self.kinds = set()

    def fresh(self, p):
        self.n += 1
        return f'{p}{p}{self.n}'

    def binder(self, p):
        """A binder's name: often `a` or `b`, shadowing the outer `let mut`s."""
        return self.rng.choice(['a', 'b']) if self.rng.random() < 0.4 else self.fresh(p)

    def expr(self, scope):
        r = self.rng
        names = sorted(scope)
        e = ('bin', r.choice(['+', '*', '-']), ('var', r.choice(names)), ('lit', r.randint(0, 9)))
        if r.random() < 0.4:
            e = ('bin', '+', e, ('var', r.choice(names)))
        return e

    def stmts(self, d, scope, muts):
        out = []
        for _ in range(self.rng.randint(1, 3)):
            s, scope, muts = self.stmt(d, scope, muts)
            out.append(s)
        return out, scope

    def without(self, scope, muts, x):
        return scope - {x}, [m for m in muts if m != x]

    def stmt(self, d, scope, muts):
        r = self.rng
        choices = [c for c in STATEMENTS if c in self.constructs]
        if 'assign' in choices:
            choices.append('assign')
        if d > 0:
            choices += [c for c in NESTING if c in self.constructs]
        c = r.choice(choices)
        if c in ('assign', 'bindassign', 'rebind', 'modify') and not muts:
            c = 'shadow'
        self.kinds.add(c)
        if c == 'assign':
            e = self.expr(scope) if r.random() >= 0.3 else ('lit', r.randint(0, 9))
            return ('assign', r.choice(muts), e), scope, muts
        if c == 'bindassign':
            return ('bindassign', r.choice(muts), self.expr(scope)), scope, muts
        if c == 'rebind':
            x = self.fresh('r')
            return ('rebind', r.choice(muts), x), scope | {x}, muts
        if c == 'pause':
            return ('pause',), scope, muts
        if c == 'shadow':
            v = self.binder('s')
            s2, m2 = self.without(scope, muts, v)
            return ('let', v, self.expr(scope)), s2 | {v}, m2
        cond = (self.expr(scope), r.randint(0, 20))
        if c == 'if':
            t, _ = self.stmts(d - 1, scope, muts)
            f, _ = self.stmts(d - 1, scope, muts)
            return ('if', cond, t, f), scope, muts
        if c in ('lethead', 'match', 'block', 'borrow', 'run'):
            x = self.binder('t')
            s2, m2 = self.without(scope, muts, x)
            s2 = s2 | {x}
        if c == 'lethead':
            t, te = self.stmts(d - 1, scope, muts)
            f, fe = self.stmts(d - 1, scope, muts)
            return ('lethead', x, cond, t, self.expr(te), f, self.expr(fe)), s2, m2
        if c == 'match':
            # The arm's binder is `()`: inside the arm its name is no integer.
            p = self.binder('p')
            sp, mp = self.without(scope, muts, p)
            if not sp:
                p = self.fresh('p'); sp, mp = scope, muts
            t, te = self.stmts(d - 1, sp, mp)
            f, fe = self.stmts(d - 1, sp, mp)
            side = r.choice(['inl', 'inr'])
            return ('match', x, side, p, t, self.expr(te), f, self.expr(fe)), s2, m2
        if c in ('for', 'gen'):
            i = self.binder('i')
            si, mi = self.without(scope, muts, i)
            b, _ = self.stmts(d - 1, si | {i}, mi)
            return (c, i, r.randint(0, 3), b), scope, muts
        if c == 'while':
            b, _ = self.stmts(d - 1, scope, muts)
            return ('while', self.fresh('w'), r.randint(0, 3), b), scope, muts
        if c == 'block':
            u = self.binder('u')
            su, mu = self.without(scope, muts, u)
            b, be = self.stmts(d - 1, su | {u}, mu)
            return ('block', x, u, b, self.expr(be)), s2, m2
        if c == 'modify':
            # The place is lent to the callback: its body does not name it.
            v = r.choice(muts)
            u = self.binder('u')
            su, mu = self.without(scope, muts, v)
            su, mu = self.without(su, mu, u)
            b, _ = self.stmts(d - 1, su | {u}, mu)
            return ('modify', v, u, b, r.randint(0, 9)), scope, muts
        if c == 'borrow':
            m = self.binder('m')
            sm, mm = self.without(scope, muts, m)
            if not sm:
                m = self.fresh('m'); sm, mm = scope, muts
            b, be = self.stmts(d - 1, sm, mm)
            return ('borrow', x, m, b, self.expr(be)), s2, m2
        if c == 'with':
            b, _ = self.stmts(d - 1, scope, muts)
            return ('with', b), scope, muts
        if c == 'run':
            b, be = self.stmts(d - 1, scope, muts)
            return ('run', x, b, self.expr(be)), s2, m2
        raise AssertionError(c)

    def program(self):
        body, _ = self.stmts(self.depth, {'a', 'b'}, ['a', 'b'])
        return body


def uses(tree, kind):
    if isinstance(tree, list):
        return any(uses(t, kind) for t in tree)
    if isinstance(tree, tuple):
        return (bool(tree) and tree[0] == kind) or any(uses(t, kind) for t in tree)
    return False


class Render:
    """The program's text. `spell` maps each name in scope to how a read of it is written: the
    name, or in the State form `ha.get()` for an outer `let mut` not shadowed."""

    def __init__(self, state):
        self.state, self.n = state, 0

    def tmp(self):
        self.n += 1
        return f'zz{self.n}'

    def expr(self, e, spell):
        if e[0] == 'lit':
            return str(e[1])
        if e[0] == 'var':
            return spell[e[1]]
        return f'({self.expr(e[2], spell)} {e[1]} {self.expr(e[3], spell)})'

    def stmts(self, ss, spell):
        out = []
        for s in ss:
            t, spell = self.stmt(s, spell)
            out.append(t)
        return '; '.join(out), spell

    def seq(self, ss, spell, tail=None):
        t, sp2 = self.stmts(ss, spell)
        return f'{t}; {"()" if tail is None else self.expr(tail, sp2)}'

    def stmt(self, s, spell):
        k, st = s[0], self.state

        def bind(x):
            s2 = dict(spell); s2[x] = x
            return s2

        def drop(x):
            return {q: v for q, v in spell.items() if q != x}

        def cond(c):
            return f'{self.expr(c[0], spell)} < {c[1]}'
        if k == 'assign':
            e = self.expr(s[2], spell)
            return (f'h{s[1]}.put({e})' if st else f'{s[1]} = {e}'), spell
        if k == 'bindassign':
            e = self.expr(s[2], spell)
            if st:
                z = self.tmp()
                return f'{z} <- return {e}; h{s[1]}.put({z})', spell
            return f'{s[1]} <- return {e}', spell
        if k == 'rebind':
            v, x = s[1], s[2]
            if st:
                z = self.tmp()
                return f'let ({z}, {x}) = bump({spell[v]}); h{v}.put({z})', bind(x)
            return f'let ({v}, {x}) = bump({v})', bind(x)
        if k == 'pause':
            return 'pause()', spell
        if k == 'let':
            return f'let {s[1]} = {self.expr(s[2], spell)}', bind(s[1])
        if k == 'if':
            return f'if {cond(s[1])} {{ {self.seq(s[2], spell)} }} else {{ {self.seq(s[3], spell)} }}', spell
        if k == 'lethead':
            x, c, t, te, f, fe = s[1:]
            return (f'let {x} = if {cond(c)} {{ {self.seq(t, spell, te)} }} '
                    f'else {{ {self.seq(f, spell, fe)} }}'), bind(x)
        if k == 'match':
            x, side, p, t, te, f, fe = s[1:]
            sp = drop(p)
            return (f'let {x} = match ({side} () : 1 + 1) {{ inl {p} -> {self.seq(t, sp, te)} '
                    f'| inr {p} -> {self.seq(f, sp, fe)} }}'), bind(x)
        if k == 'for':
            i, n, b = s[1:]
            return f'for {i} in 0..{n} {{ {self.seq(b, bind(i))} }}', spell
        if k == 'gen':
            i, n, b = s[1:]
            return f'for {i} in upto({n}) {{ {self.seq(b, bind(i))} }}', spell
        if k == 'while':
            w, n, b = s[1:]
            return f'let mut {w} = 0; while {w} < {n} {{ {w} = {w} + 1; {self.seq(b, spell)} }}', spell
        if k == 'block':
            x, u, b, be = s[1:]
            return f'let {x} = ap(!{{ {u} -> {self.seq(b, bind(u), be)} }})', bind(x)
        if k == 'modify':
            v, u, b, kk = s[1:]
            su = drop(v); su[u] = u
            tail = ('bin', '+', ('var', u), ('lit', kk))
            return f'modify &mut {v} {{ {u} -> {self.seq(b, su, tail)} }}', spell
        if k == 'borrow':
            x, m, b, be = s[1:]
            return f'let {x} = borrow mut cell {{ {m} -> {self.seq(b, drop(m), be)} }}', bind(x)
        if k == 'with':
            return f'with resuming {{ {self.seq(s[1], spell)} }}', spell
        if k == 'run':
            x, b, be = s[1:]
            t, sp2 = self.stmts(b, spell)
            return f'let {x} = run ({t}; return {self.expr(be, sp2)})', bind(x)
        raise AssertionError(k)


def render(body, state):
    R = Render(state)
    spell = {'a': 'ha.get()', 'b': 'hb.get()'} if state else {'a': 'a', 'b': 'b'}
    text, sp2 = R.stmts(body, spell)
    fa, fb = sp2['a'], sp2['b']
    head = HEAD + (GEN_HEAD if uses(body, 'gen') else '')
    cell = uses(body, 'borrow')
    pre = '  let cell = alloc(0);\n' if cell else ''
    post = '  let _ = free(cell);\n' if cell else ''
    if not state:
        return (head + 'fn body() -> i32 * i32 with Pause =\n  let mut a = 1;\n  let mut b = 2;\n'
                + pre + f'  {text};\n' + post +
                f'  ({fa}, {fb})\n\nmain -> i32 * i32 = with resuming {{ body() }}\n')
    return (head + 'fn body() -> i32 * i32 with Pause =\n'
            '  let (r, b) = with hb = state[i32, (i32 * i32) * i32](2) {\n'
            '    with ha = state[i32, i32 * i32](1) {\n'
            f'      {text};\n      ({fa}, {fb})\n    }}\n  }};\n'
            '  let (v, a) = r;\n  v\n\nmain -> i32 * i32 = with resuming { body() }\n')


class Cell:
    def __init__(self, v):
        self.v = v


class Eval:
    """The meaning SPEC §41 gives a program: each binder a variable of its own, in scope to the end
    of its block; an assignment updates the variable its name resolves to."""

    def expr(self, e, env):
        if e[0] == 'lit':
            return e[1]
        if e[0] == 'var':
            return env[e[1]].v
        a, b = self.expr(e[2], env), self.expr(e[3], env)
        return wrap({'+': a + b, '-': a - b, '*': a * b}[e[1]])

    def stmts(self, ss, env):
        env = dict(env)
        for s in ss:
            env = self.stmt(s, env)
        return env

    def seq(self, ss, env, tail=None):
        env2 = self.stmts(ss, env)
        return None if tail is None else self.expr(tail, env2)

    def stmt(self, s, env):
        k = s[0]

        def bind(x, v):
            e2 = dict(env); e2[x] = Cell(v)
            return e2

        def drop(x):
            return {q: c for q, c in env.items() if q != x}
        if k in ('assign', 'bindassign'):
            env[s[1]].v = self.expr(s[2], env)
            return env
        if k == 'rebind':
            old = env[s[1]].v
            env[s[1]].v = wrap(old + 1)
            return bind(s[2], old)
        if k == 'pause':
            return env
        if k == 'let':
            return bind(s[1], self.expr(s[2], env))
        if k == 'if':
            (ce, ck), t, f = s[1:]
            self.seq(t if self.expr(ce, env) < ck else f, env)
            return env
        if k == 'lethead':
            x, (ce, ck), t, te, f, fe = s[1:]
            yes = self.expr(ce, env) < ck
            return bind(x, self.seq(t, env, te) if yes else self.seq(f, env, fe))
        if k == 'match':
            x, side, p, t, te, f, fe = s[1:]
            ep = drop(p)
            return bind(x, self.seq(t, ep, te) if side == 'inl' else self.seq(f, ep, fe))
        if k in ('for', 'gen'):
            i, n, b = s[1:]
            for j in range(n):
                e2 = dict(env); e2[i] = Cell(j)
                self.seq(b, e2)
            return env
        if k == 'while':
            for _ in range(s[2]):
                self.seq(s[3], env)
            return env
        if k == 'block':
            x, u, b, be = s[1:]

            def call(arg):
                e2 = dict(env); e2[u] = Cell(arg)
                return self.seq(b, e2, be)
            r1 = call(1)
            r2 = call(2)
            return bind(x, wrap(r1 * 10 + r2))
        if k == 'modify':
            v, u, b, kk = s[1:]
            eu = drop(v); eu[u] = Cell(env[v].v)
            env[v].v = self.seq(b, eu, ('bin', '+', ('var', u), ('lit', kk)))
            return env
        if k == 'borrow':
            x, m, b, be = s[1:]
            return bind(x, self.seq(b, drop(m), be))
        if k == 'with':
            self.seq(s[1], env)
            return env
        if k == 'run':
            x, b, be = s[1:]
            return bind(x, self.seq(b, env, be))
        raise AssertionError(k)

    def program(self, body):
        env = self.stmts(body, {'a': Cell(1), 'b': Cell(2)})
        return f'(i32[{env["a"].v & M32}], i32[{env["b"].v & M32}])'


def run(bcc, path):
    p = subprocess.run([bcc, 'interp', path], capture_output=True, text=True, timeout=300)
    if p.returncode != 0:
        out = (p.stdout + p.stderr).strip()
        return None, out.splitlines()[0] if out else 'failed'
    return p.stdout.strip().splitlines()[0], None


def check(bcc, d, k, body, kinds):
    pm = os.path.join(d, f'c{k}.bc')
    open(pm, 'w').write(render(body, False))
    want = Eval().program(body)
    vm, em = run(bcc, pm)
    st = None
    if kinds <= STATE_OK:
        ps = os.path.join(d, f'c{k}.state.bc')
        open(ps, 'w').write(render(body, True))
        st = run(bcc, ps)
    return pm, want, vm, em, st


def row(bcc, name, constructs, a, tmp, rng):
    tally = {'agree': 0, 'differ': 0, 'refused': 0, 'State form run': 0, 'State form differs': 0}
    reasons = {}
    kinds = set()
    progs = []
    for k in range(a.count):
        g = Gen(rng, a.depth, constructs)
        body = g.program()
        kinds |= g.kinds
        progs.append((k, body, g.kinds))
    d = os.path.join(tmp, name)
    os.makedirs(d, exist_ok=True)
    with ThreadPoolExecutor(a.jobs) as ex:
        res = list(ex.map(lambda p: check(bcc, d, *p), progs))
    for pm, want, vm, em, st in res:
        if vm is None:
            tally['refused'] += 1
            reasons.setdefault(em.split(': ', 1)[-1][:110], []).append(pm)
        elif vm != want:
            tally['differ'] += 1
            print(f'DIFFER {pm}: let mut {vm}, expected {want}')
        else:
            tally['agree'] += 1
        if st is not None:
            tally['State form run'] += 1
            vs, es = st
            if vs != want:
                tally['State form differs'] += 1
                print(f'STATE {pm[:-3]}.state.bc: {vs if vs is not None else es}, expected {want}')
    print(f'row {name}: seed {a.seed}, {a.count} programs, depth {a.depth}, '
          f'constructs {sorted(kinds)}')
    for k, v in tally.items():
        print(f'  {k}: {v}')
    for r, fs in sorted(reasons.items(), key=lambda kv: -len(kv[1])):
        print(f'  refused {len(fs)} ({os.path.basename(fs[0])}): {r}')
    return tally['differ'] + tally['refused'] + tally['State form differs']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, default=611)
    ap.add_argument('--count', type=int, default=200)
    ap.add_argument('--depth', type=int, default=3)
    ap.add_argument('--keep', default=None)
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--constructs', default=','.join(ALL))
    ap.add_argument('--without', default='', help='constructs to leave out, comma-separated')
    ap.add_argument('--bcc', default=None, help='the compiler to run (default: the build)')
    ap.add_argument('--gate', action='store_true',
                    help="the gate's rows (`ROWS`); fails on any difference or refusal")
    a = ap.parse_args()
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    bcc = a.bcc or os.path.join(root, '.lake/build/bin/bcc')
    tmp = a.keep or tempfile.mkdtemp()
    os.makedirs(tmp, exist_ok=True)
    rng = random.Random(a.seed)
    if a.gate:
        rows = ROWS
    else:
        out = set(a.without.split(','))
        rows = [('all', [c for c in a.constructs.split(',') if c and c not in out])]
    bad = sum(row(bcc, name, set(cs), a, tmp, rng) for name, cs in rows)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
