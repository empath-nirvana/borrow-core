import os,re,sys,json,collections
PAT={
 'RefCell<':r'\bRefCell\s*<',
 'Cell< (plain)':r'(?<![A-Za-z0-9_])Cell\s*<',
 'Rc<RefCell':r'\bRc\s*<\s*RefCell\b',
 'Arc<Mutex|RwLock':r'\bArc\s*<\s*(Mutex|RwLock)\b',
 'UnsafeCell<':r'\bUnsafeCell\s*<',
 'OnceCell':r'\bOnceCell\b',
 'OnceLock':r'\bOnceLock\b',
 'LazyCell':r'\bLazyCell\b',
 'LazyLock':r'\bLazyLock\b',
 'Lazy< (once_cell)':r'(?<![A-Za-z0-9_])Lazy\s*<',
 'lazy_static!':r'\blazy_static!',
 'thread_local!':r'\bthread_local!',
 'Mutex<':r'\bMutex\s*<',
 'RwLock<':r'\bRwLock\s*<',
 'Atomic*':r'\bAtomic(Bool|Usize|Isize|U8|U16|U32|U64|I8|I16|I32|I64|Ptr)\b',
}
C={k:re.compile(v) for k,v in PAT.items()}
def is_testpath(p):
    return bool(re.search(r'/(tests|benches|examples|testdata|test)/',p)) or os.path.basename(p).startswith('test')
def run(root, label, crate_depth=1):
    occ=collections.Counter(); occ_t=collections.Counter(); files=collections.defaultdict(set); crates=collections.defaultdict(set); total_crates=set(); nfiles=0; nlines=0
    for dp,dn,fn in os.walk(root):
        for f in fn:
            if not f.endswith('.rs'): continue
            p=os.path.join(dp,f); rel=os.path.relpath(p,root); crate=rel.split(os.sep)[0] if crate_depth==1 else '/'.join(rel.split(os.sep)[:crate_depth])
            total_crates.add(crate)
            try: lines=open(p,encoding='utf-8',errors='replace').read().split('\n')
            except: continue
            nfiles+=1; nlines+=len(lines)
            tp=is_testpath('/'+rel); cfgt=None
            for i,l in enumerate(lines):
                if cfgt is None and '#[cfg(test)]' in l: cfgt=i
                s=l.strip()
                if s.startswith('//'): continue
                for k,c in C.items():
                    n=len(c.findall(l))
                    if n:
                        occ[k]+=n; files[k].add(p); crates[k].add(crate)
                        if tp or (cfgt is not None and i>=cfgt): occ_t[k]+=n
    print(f'## {label}: {len(total_crates)} crates, {nfiles} .rs files, {nlines} lines')
    print(f'| pattern | occurrences | in test code (heur.) | files | crates |')
    for k in PAT: print(f'| {k} | {occ[k]} | {occ_t[k]} | {len(files[k])} | {len(crates[k])} |')
    return crates
if __name__=='__main__':
    root,label=sys.argv[1],sys.argv[2]; depth=int(sys.argv[3]) if len(sys.argv)>3 else 1
    cr=run(root,label,depth)
    json.dump({k:sorted(v) for k,v in cr.items()},open(sys.argv[4] if len(sys.argv)>4 else '/dev/null','w'))
