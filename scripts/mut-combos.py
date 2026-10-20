#!/usr/bin/env python3
"""Differential check of `let mut` (#611): random nestings of `if`, `match`, `for`, blocks passed
to a function that calls them twice, shadowing `let`s and `pause()` (a control operation that
captures and resumes), each assigning the outer `let mut`s `a` and `b`. Each program is written
twice: with `let mut`, as the elaborator threads it, and with `a` and `b` instances of the
ordinary control effect `State` (`ha.get()`, `ha.put(v)`), which the kernel runs as handlers.
Both are run by `bcc interp`; a program whose two runs answer differently is a wrong answer of
one of them.

    scripts/mut-combos.py [--seed N] [--count N] [--depth N] [--keep DIR]
"""
import argparse, os, random, subprocess, sys, tempfile

HEAD = '''effect State[T] { linear ctl get() -> T; linear ctl put(v: T) }

handler state[T, A](mut s: T): State[T], A -> A * T = {
  return(a) = (a, s);
  get(k) = k(s);
  put(v, k) = { s = v; k(()) }
}

effect Pause { ctl pause() }

handler resuming[A]: Pause, A -> A = { return(a) = a; pause(k) = k(()) }

fn ap(f: !(i32 => i32)) -> i32 = f(1) * 10 + f(2)
'''

class Gen:
    def __init__(self, rng, depth, without=()):
        self.rng, self.depth, self.n, self.without = rng, depth, 0, set(without)
        self.kinds = set()

    def fresh(self, p):
        self.n += 1
        return f'{p}{p}{self.n}'

    # An expression over the variables in scope: `env` maps a surface name to its two spellings.
    def expr(self, env):
        r = self.rng
        names = list(env)
        x = r.choice(names)
        k = r.randint(0, 9)
        op = r.choice(['+', '*', '-'])
        y = r.choice(names)
        m = (f'{env[x][0]} {op} {k}', f'{env[x][1]} {op} {k}')
        if r.random() < 0.4:
            m = (f'({m[0]}) + {env[y][0]}', f'({m[1]}) + {env[y][1]}')
        return m

    # A sequence of statements; `muts` are the assignable outer names still visible.
    def stmts(self, d, env, muts):
        out_m, out_s = [], []
        env = dict(env)
        muts = list(muts)
        for _ in range(self.rng.randint(1, 3)):
            m, s, env, muts = self.stmt(d, env, muts)
            out_m.append(m); out_s.append(s)
        if out_m[-1].startswith('let '):
            out_m.append('()'); out_s.append('()')
        self.last_env = env
        return '; '.join(out_m), '; '.join(out_s), env

    def stmt(self, d, env, muts):
        r = self.rng
        choices = ['assign', 'assign']
        if d > 0:
            choices += ['if', 'lethead', 'match', 'for', 'block']
        choices += ['shadow', 'pause']
        choices = [c for c in choices if c not in self.without]
        c = r.choice(choices)
        if c == 'assign' and not muts:
            c = 'pause'
        self.kinds.add(c)
        if c == 'assign':
            v = r.choice(muts)
            e = self.expr(env)
            if r.random() < 0.3:
                k = str(r.randint(0, 9)); e = (k, k)
            return f'{v} = {e[0]}', f'h{v}.put({e[1]})', env, muts
        if c == 'pause':
            return 'pause()', 'pause()', env, muts
        if c == 'shadow':
            v = r.choice(['a', 'b'])
            e = self.expr(env)
            env2 = dict(env); env2[v] = (v, v)
            return f'let {v} = {e[0]}', f'let {v} = {e[1]}', env2, [x for x in muts if x != v]
        cond_e = self.expr(env)
        k = r.randint(0, 20)
        cm, cs = f'{cond_e[0]} < {k}', f'{cond_e[1]} < {k}'
        if c == 'if':
            t = self.stmts(d - 1, env, muts); f = self.stmts(d - 1, env, muts)
            return (f'if {cm} {{ {t[0]} }} else {{ {f[0]} }}',
                    f'if {cs} {{ {t[1]} }} else {{ {f[1]} }}', env, muts)
        if c == 'lethead':
            t = self.stmts(d - 1, env, muts); f = self.stmts(d - 1, env, muts)
            et, ef = self.expr(t[2]), self.expr(f[2])
            x = self.fresh('t')
            env2 = dict(env); env2[x] = (x, x)
            return (f'let {x} = if {cm} {{ {t[0]}; {et[0]} }} else {{ {f[0]}; {ef[0]} }}',
                    f'let {x} = if {cs} {{ {t[1]}; {et[1]} }} else {{ {f[1]}; {ef[1]} }}', env2, muts)
        if c == 'match':
            t = self.stmts(d - 1, env, muts); f = self.stmts(d - 1, env, muts)
            et, ef = self.expr(t[2]), self.expr(f[2])
            x = self.fresh('t')
            s = r.choice(['inl ()', 'inr ()'])
            env2 = dict(env); env2[x] = (x, x)
            return (f'let {x} = match ({s} : 1 + 1) {{ inl u -> {t[0]}; {et[0]} | inr u -> {f[0]}; {ef[0]} }}',
                    f'let {x} = match ({s} : 1 + 1) {{ inl u -> {t[1]}; {et[1]} | inr u -> {f[1]}; {ef[1]} }}',
                    env2, muts)
        if c == 'for':
            i = self.fresh('i')
            env2 = dict(env); env2[i] = (i, i)
            b = self.stmts(d - 1, env2, muts)
            n = r.randint(0, 3)
            return f'for {i} in 0..{n} {{ {b[0]}; () }}', f'for {i} in 0..{n} {{ {b[1]}; () }}', env, muts
        if c == 'block':
            u = self.fresh('u')
            env2 = {u: (u, u)}
            b = self.stmts(d - 1, env2, muts)
            e = self.expr(b[2])
            x = self.fresh('t')
            env3 = dict(env); env3[x] = (x, x)
            return (f'let {x} = ap(!{{ {u} -> {b[0]}; {e[0]} }})',
                    f'let {x} = ap(!{{ {u} -> {b[1]}; {e[1]} }})', env3, muts)
        raise AssertionError(c)

    def program(self):
        env = {'a': ('a', 'ha.get()'), 'b': ('b', 'hb.get()')}
        m, s, _ = self.stmts(self.depth, env, ['a', 'b'])
        fa, fb = self.last_env['a'], self.last_env['b']
        mut = (HEAD + 'fn body() -> i32 * i32 with Pause =\n  let mut a = 1;\n  let mut b = 2;\n'
               f'  {m};\n  ({fa[0]}, {fb[0]})\n\nmain -> i32 * i32 = with resuming {{ body() }}\n')
        st = (HEAD + 'fn body() -> i32 * i32 with Pause =\n'
              '  let (r, b) = with hb = state[i32, (i32 * i32) * i32](2) {\n'
              '    with ha = state[i32, i32 * i32](1) {\n'
              f'      {s};\n      ({fa[1]}, {fb[1]})\n    }}\n  }};\n'
              '  let (v, a) = r;\n  v\n\nmain -> i32 * i32 = with resuming { body() }\n')
        return mut, st

def run(bcc, path):
    p = subprocess.run([bcc, 'interp', path], capture_output=True, text=True, timeout=120)
    if p.returncode != 0:
        return None, (p.stdout + p.stderr).strip().splitlines()[0] if (p.stdout + p.stderr).strip() else 'failed'
    return p.stdout.strip().splitlines()[0], None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, default=611)
    ap.add_argument('--count', type=int, default=200)
    ap.add_argument('--depth', type=int, default=3)
    ap.add_argument('--keep', default=None)
    ap.add_argument('--without', default='', help='constructs to leave out, comma-separated')
    a = ap.parse_args()
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    bcc = os.path.join(root, '.lake/build/bin/bcc')
    rng = random.Random(a.seed)
    tmp = a.keep or tempfile.mkdtemp()
    os.makedirs(tmp, exist_ok=True)
    tally = {'agree': 0, 'differ': 0, 'mut refused': 0, 'state refused': 0, 'both refused': 0}
    kinds = set()
    reasons = {}
    for k in range(a.count):
        g = Gen(rng, a.depth, [c for c in a.without.split(',') if c])
        mut, st = g.program()
        kinds |= g.kinds
        pm, ps = os.path.join(tmp, f'c{k}.bc'), os.path.join(tmp, f'c{k}.state.bc')
        open(pm, 'w').write(mut); open(ps, 'w').write(st)
        (vm, em), (vs, es) = run(bcc, pm), run(bcc, ps)
        if vm is not None and vs is not None:
            if vm == vs:
                tally['agree'] += 1
            else:
                tally['differ'] += 1
                print(f'DIFFER {pm}: let mut {vm}, State {vs}')
        elif vm is None and vs is None:
            tally['both refused'] += 1
            reasons.setdefault('both: ' + em.split(': ', 1)[-1][:90], []).append(pm)
        elif vm is None:
            tally['mut refused'] += 1
            reasons.setdefault('mut: ' + em.split(': ', 1)[-1][:90], []).append(pm)
        else:
            tally['state refused'] += 1
            reasons.setdefault('state: ' + es.split(': ', 1)[-1][:90], []).append(ps)
    print(f'seed {a.seed}, {a.count} programs, depth {a.depth}, constructs {sorted(kinds)}')
    for k, v in tally.items():
        print(f'  {k}: {v}')
    for r, fs in sorted(reasons.items(), key=lambda kv: -len(kv[1])):
        print(f'  refused {len(fs)} ({os.path.basename(fs[0])}): {r}')
    return 1 if tally['differ'] else 0

if __name__ == '__main__':
    sys.exit(main())
