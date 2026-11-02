"""Run `Deps.lean` once per library root and merge the outputs into `.lake/corec-gen/`
(`deps.txt`, `all.txt`, `iface.txt`). The library's leaf modules cannot all be imported into one
environment, so each root is analysed on its own; whether a declaration is dependent is a property
of the declaration, so the union is the library's answer. Run from the repository root. A root whose own import fails is skipped and reported."""
import os
import subprocess

R = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')) + '/'
D = R + '.lake/corec-gen/'
ROOTS = ['Fundamental', 'AwaitCancel', 'BlockPrograms', 'ClauseOwn', 'CloPrograms', 'DeclLend',
         'DelayNaive', 'DivDrive', 'DivRuntime', 'EffCancelRuns', 'Mentions', 'NestedPrograms',
         'Rejections', 'ReuseList', 'Stdio', 'StreamPrograms']
os.makedirs(D, exist_ok=True)
body = open(R + 'experiments/DtorUnwind/corec-gen/Deps.lean').read()
for r in ROOTS:
    f = D + 'Deps_%s.lean' % r
    open(f, 'w').write(body.replace('import Core.Fundamental', 'import Core.' + r, 1))
    if os.path.exists(D + 'deps-%s.txt' % r):
        continue
    p = subprocess.run(['lake', 'env', 'lean', f], cwd=R, env=dict(os.environ, COREC_TAG=r))
    if p.returncode != 0:
        print('SKIPPED (does not import on its own):', r)
ROOTS = [r for r in ROOTS if os.path.exists(D + 'deps-%s.txt' % r)]
for k in ['deps', 'all', 'iface']:
    lines = set()
    for r in ROOTS:
        lines |= set(l for l in open(D + '%s-%s.txt' % (k, r)).read().split('\n') if l.strip())
    open(D + k + '.txt', 'w').write('\n'.join(sorted(lines)))
