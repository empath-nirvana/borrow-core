"""Port Core/Invariant.lean and Core/Images.lean pieces to the tree world (TreeWp): port.py's carrier
translation, then the record layer (FrameRec -> FrameRecT, VTy -> KTy, vShape -> interp) and the
TreeWp names of the invariant's clauses.
usage: tinv.py OUT IMPORT -- SRC:a-b ..."""
import re, sys, subprocess, os
here = os.path.dirname(os.path.abspath(__file__))
out = sys.argv[1]; imp = sys.argv[2]; srcs = sys.argv[4:]
tmp = out + '.tmp'
# lifetimes stay `Life` over the tree (port.py reads printed `Life` binders as cell lifetime sets)
body = []
for spec in srcs:
    f, rng = spec.split(':'); a, b = map(int, rng.split('-'))
    body.append('\n'.join(open(f).read().split('\n')[a-1:b]))
src = tmp + '.src'
open(src, 'w').write('\n'.join(body).replace(': Life', ': LifeKEEP'))
subprocess.run(['python3', os.path.join(here, 'port.py'), tmp, imp, '--', src], check=True)
os.remove(src)
s = open(tmp).read().replace('LifeKEEP', 'Life'); os.remove(tmp)
s = s.replace('import ' + imp + '\n\nnoncomputable section\n', '')
s = re.sub(r'\nend\n*$', '\n', s)
s = s.replace('(ResUT BoCa.Loc BoCa.Val K)', 'TRes K').replace('CellUT Loc Val K', 'TCell K')
s = re.sub(r'List FrameRec\b', 'List (FrameRecT K)', s); s = re.sub(r'\bFrameRec\b', 'FrameRecT K', s)
s = re.sub(r'\bVTy\b', 'KTy', s)
for a in ['RefPos', 'MutPos', 'Chain', 'GPos', 'SubRec', 'LinPath', 'DescR', 'Desc', 'LinLoc', 'Root', 'Class', 'Coverage', 'NoMut', 'LeInv', 'MutAt']:
    s = re.sub(r'(?<![\w.])' + a + r'(?=[\s.)])', a + 'T', s)
for a in ['ChainInv', 'DeepInv', 'JointAt', 'JointDeep']:
    s = re.sub(r'(?<![\w.])' + a + r' ', a + 'T K Θ ', s)
s = re.sub(r'(?<![\w.])NestLifeT? ', 'NestLifeT K ', s)
s = re.sub(r'(?<![\w.])TI ', 'TIT K Θ ', s)
s = re.sub(r'\bLoc\b', 'BoCa.Loc', s).replace('BoCa.BoCa.Loc', 'BoCa.Loc')
s = re.sub(r'(?<![\w.])Val\b', 'BoCa.Val', s).replace('BoCa.BoCa.Val', 'BoCa.Val')
s = s.replace('(Loc := BoCa.Loc)', '(Loc := BoCa.Loc)')
s = re.sub(r"(?<![\w.])([a-zα-ω][\w'₀-₉]*)\.mem ([\w'₀-₉]+)", r"\2 ∈ \1.set", s)
s = s.replace('List TRes K', 'List (TRes K)').replace('(TSet.single α).join', '(TSet.single α)')
s = re.sub(r"(?<![\w.])([\w'₀-₉]+) ⊏ ([\w'₀-₉]+)", r"K.lt \1 \2", s)
s = re.sub(r"(?<![\w.])([\w'₀-₉]+) ⊑ ([\w'₀-₉]+)", r"K.le \1 \2", s)
s = s.replace('LSet.singleton', 'TSet.single')
s = re.sub(r'(InStratum \(TSet\.single [^()]*\))\.join', r'\1', s)
s = re.sub(r'\bCellUT\.lsOf_immOf\b', 'CellUT.lsOfI_immOf', s)
hdr = f'''import {imp}

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {{K : WCactus}}

'''
open(out, 'w').write(hdr + s.strip() + '\n\nend BoCa.Fig16.Tree.Wp\n\nend\n')
