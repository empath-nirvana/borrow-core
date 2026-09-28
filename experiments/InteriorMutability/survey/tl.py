import os,re,sys
R={'RefCell<':re.compile(r'\bRefCell\s*<'),'Cell<':re.compile(r'(?<![A-Za-z0-9_])Cell\s*<'),'OnceCell':re.compile(r'\bOnceCell\b')}
tot={k:0 for k in R}; intl={k:0 for k in R}; tlblocks=0
for root in sys.argv[1:]:
  for dp,dn,fn in os.walk(root):
    for f in fn:
      if not f.endswith('.rs'): continue
      s=open(os.path.join(dp,f),encoding='utf-8',errors='replace').read()
      s2=re.sub(r'//[^\n]*','',s)
      spans=[]
      for m in re.finditer(r'thread_local!\s*([\{\(\[])',s2):
        o=m.group(1); c={'{':'}','(':')','[':']'}[o]; d=0; i=m.end()-1
        while i<len(s2):
          if s2[i]==o: d+=1
          elif s2[i]==c:
            d-=1
            if d==0: break
          i+=1
        spans.append((m.start(),i)); tlblocks+=1
      for m in re.finditer(r'#\[thread_local\][^;]*;',s2): spans.append((m.start(),m.end()))
      for k,r in R.items():
        for m in r.finditer(s2):
          tot[k]+=1
          if any(a<=m.start()<=b for a,b in spans): intl[k]+=1
print('thread_local! blocks:',tlblocks)
for k in R: print(k,'total',tot[k],'inside thread_local',intl[k], f'{100*intl[k]/max(1,tot[k]):.1f}%')
