"""Generate `experiments/DtorUnwind/DtorUnwind/CoreC/`: the library's world-dependent declarations
over canonical-image worlds.

Input: `.lake/corec-gen/{deps,all}.txt` from `Deps.lean`. For each library module holding a
dependent declaration, the copy keeps the module's text with every non-dependent declaration
removed (those stay the library's, reached through the parent namespace), and:

* namespace `Core` becomes `Core.C`; a nested namespace `Core.X` becomes `Core.C.X`, opening and
  re-exporting `Core.X`'s non-dependent names so they win over `Core`'s (a relative `namespace X`
  inside `Core` likewise);
* `TW` becomes `DtorUnwind.SI.TWNC` (`DivHandleLast`'s operation-table variable named `TW` is
  renamed first);
* the notation `vC` becomes `vCc`, declared after the copy's `vCE`;
* an `open` of a library namespace holding dependent declarations opens their copies;
* dot calls of dependent declarations in a non-dependent type's namespace (`o.ent δ`,
  `hS.abort`, …) are written out, so they resolve to the copy;
* the world's interface (`iface.txt`: declarations that are not dependent but mention `TW`, such
  as `coh_mut`, `tags_above`, `tagged_reb`, `alloc_world`, `ownWorld`) is copied too, except
  `TW.valid`/`TW.inv`/`TW.linLife`, which `TWNC` has;
* `rebChooseTW_top` and `rebChooseTW_deep` are not copied: `CoreC/CanonChoose.lean` gives them
  at canonical images, and every module importing the copy of `Core.Reborrow` imports it.

Run from the repository root: `python3 experiments/DtorUnwind/corec-gen/gen.py`.
"""
import os
import re

R = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')) + '/'
D = R + '.lake/corec-gen/'
OUT = R + 'experiments/DtorUnwind/DtorUnwind/CoreC/'
P = 'BoCa.Fig16.LogRel.Core.'

ALL = [l.split() for l in open(D + 'all.txt') if l.strip()]
ALLMOD = {n: m for m, _, _, n in ALL}

dep = {}
for l in open(D + 'deps.txt'):
    if not l.strip():
        continue
    m, a, b, n = l.split()
    if n.startswith(P + 'TW.'):
        continue
    dep[n] = m

IFACE = [n[len(P):] for _, n in (l.split() for l in open(D + 'iface.txt') if l.strip())
         if n.startswith(P) and n != P + 'TW' and not n.startswith(P + 'TW.')]
EXCL = ['rebChooseTW_top', 'rebChooseTW_deep']
for m, a, b, n in ALL:
    if n[len(P):] in IFACE:
        dep[n] = m
for k in EXCL:
    dep.pop(P + k, None)

deprng = {}
for m, a, b, n in ALL:
    if n in dep:
        deprng.setdefault(m, []).append((int(a), int(b)))
depmods = set(dep.values())
nondep = {}
for m, a, b, n in ALL:
    if m in depmods and n not in dep and '_private' not in n:
        nondep.setdefault(m, []).append((int(a), int(b)))


def imports(m):
    return [l.split()[1] for l in open(R + m.replace('.', '/') + '.lean') if l.startswith('import ')]


def closure(ms):
    seen, st = set(), [i for i in ms if i.startswith('Core.')]
    while st:
        x = st.pop()
        if x in seen:
            continue
        seen.add(x)
        st += [y for y in imports(x) if y.startswith('Core.')]
    return seen


def export_line(mm, visible):
    X = mm.group(1)
    pre = P + X + '.'
    ex = sorted(set(n[len(pre):] for n, mod in ALLMOD.items()
                    if mod in visible and n.startswith(pre) and n not in dep
                    and not any(c.startswith('_') or c.startswith('match_') or c.startswith('proof_')
                                or c.startswith('eq_') for c in n[len(pre):].split('.'))))
    return (mm.group(0) + 'open BoCa.Fig16.LogRel.Core.' + X + '\n'
            + 'export BoCa.Fig16.LogRel.Core.' + X + ' (' + ' '.join(ex) + ')\n')


def fix_open(mm, visible):
    """An `open` of a library namespace that holds dependent declarations opens their copies."""
    X, names = mm.group(1), mm.group(2)
    pre = P + X + '.'
    depx = sorted(set(n[len(pre):] for n in dep if n.startswith(pre) and '.' not in n[len(pre):]
                      and ALLMOD.get(n) in visible
                      and not n[len(pre):].startswith('_') and 'match_' not in n))
    if not depx:
        return mm.group(0)
    if names is None:
        return ('open BoCa.Fig16.LogRel.Core.%s hiding %s\nopen BoCa.Fig16.LogRel.Core.C.%s'
                % (X, ' '.join(depx), X))
    ns = names.split()
    keep = [n for n in ns if n not in depx]
    moved = [n for n in ns if n in depx]
    out = []
    if keep:
        out.append('open BoCa.Fig16.LogRel.Core.%s (%s)' % (X, ' '.join(keep)))
    if moved:
        out.append('open BoCa.Fig16.LogRel.Core.C.%s (%s)' % (X, ' '.join(moved)))
    return '\n'.join(out)


for m in sorted(depmods):
    src = open(R + m.replace('.', '/') + '.lean').read().split('\n')
    kill = set()
    for a, b in nondep.get(m, []):
        if any(not (b < x or y < a) for x, y in deprng.get(m, [])):
            continue
        kill.update(range(a, b + 1))
        j = a - 1
        while j >= 1 and re.match(r'^(open .* in|set_option .* in|include .* in|omit .* in)\s*$',
                                  src[j - 1]):
            kill.add(j)
            j -= 1
    imps = imports(m)
    hdr = ['import ' + m] + ['import ' + i for i in imps]
    visible = closure(imps) | {m}
    for i in sorted(closure(imps)):
        if i in depmods:
            hdr.append('import DtorUnwind.CoreC.' + i[len('Core.'):])
        if i == 'Core.Reborrow':
            hdr.append('import DtorUnwind.CoreC.CanonChoose')
    if m == 'Core.World':
        hdr.append('import DtorUnwind.SI.CanonDeep')
    t = '\n'.join(line for k, line in enumerate(src, 1)
                  if not line.startswith('import ') and k not in kill)
    t = re.sub(r'^open BoCa\.Fig16\.LogRel\.Core\.(?!C\b)([^\s(]+)(?: \(([^)]*)\))?[ \t]*$', lambda mm: fix_open(mm, visible), t,
               flags=re.M)
    t = re.sub(r'^(namespace|end) BoCa\.Fig16\.LogRel\.Core(?=[.\s])',
               r'\1 BoCa.Fig16.LogRel.Core.C', t, flags=re.M)
    t = re.sub(r'^namespace BoCa\.Fig16\.LogRel\.Core\.C\.(\S+)\n', lambda mm: export_line(mm, visible), t, flags=re.M)
    t = re.sub(r'^namespace (?!BoCa\.)(\S+)\n', lambda mm: export_line(mm, visible), t, flags=re.M)
    for a, b in [('Ti TW To', 'Ti TWo To'), ('(TW To ', '(TWo To '),
                 ('lastW₂ TW To', 'lastW₂ TWo To'), ('cwp TW Q₁', 'cwp TWo Q₁')]:
        t = t.replace(a, b)
    t = re.sub(r'\bTW\b', 'DtorUnwind.SI.TWNC', t)
    t = re.sub(r"(?<![A-Za-z0-9_.])vC(?![A-Za-z0-9_'₀-₉])", 'vCc', t)
    t = t.replace('_root_.BoCa.Fig16.LogRel.Core.', '_root_.BoCa.Fig16.LogRel.Core.C.')
    if m == 'Core.Relation':
        i = t.index('\nmutual\n')
        j = t.index('\nend\n', i) + 5
        t = (t[:j] + '\n/-- `vCE none`, at the copy\'s relation. -/\nnotation "vCc" => vCE none\n'
             + t[j:])
    t = re.sub(r'\nmutual\s*\nend\n', '\n', t)
    t = re.sub(r"(?<![A-Za-z0-9_.'])(?!OpSig\.)([A-Za-z][A-Za-z0-9_']*)\.ent δ",
               r'(OpSig.ent δ \1)', t)
    t = re.sub(r"(?<![A-Za-z0-9_.'])hS\.(abort|out|tab_extend)(?![A-Za-z0-9_'])",
               r'(Row.Unwind.\1 hS)', t)
    t = re.sub(r'/--(?:(?!-/).)*?-/[ \t]*\n(?=\s*(?:/--|/-!|end\b|\Z))', '', t, flags=re.S)
    t = re.sub(r'\n{3,}', '\n\n', t)
    banner = ('/-! Generated by `experiments/DtorUnwind/corec-gen/gen.py`. `%s` over canonical-image '
              'worlds: the declarations whose statement or proof reads the world relation, with '
              '`TW` replaced by `TWNC`, in namespace `Core.C`. Every other declaration is the '
              'library\'s. -/\n' % m)
    with open(OUT + m[len('Core.'):] + '.lean', 'w') as f:
        f.write('\n'.join(hdr) + '\n\n' + banner + t)
print(' '.join(sorted(depmods)))
