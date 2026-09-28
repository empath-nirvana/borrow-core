import random,collections,sys
random.seed(20260928)
def pick(fn,n):
    g=collections.defaultdict(list)
    for l in open(fn):
        p=l.split(':')[0]; crate='/'.join(p.split('/')[:2]); g[crate].append(l.rstrip('\n'))
    crates=sorted(g); one=[random.choice(g[c]) for c in crates]
    random.shuffle(one); return one[:n], len(crates)
for fn,n,tag in [('meta/hits_refcell.txt',50,'R'),('meta/hits_cell.txt',40,'C')]:
    s,nc=pick(fn,n); print(f'# {tag} crates={nc} sampled={len(s)}')
    for i,l in enumerate(s): print(f'{tag}{i+1:02d} {l[:230]}')
