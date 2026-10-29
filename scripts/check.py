#!/usr/bin/env python3
"""Added by cx on 2026-10-29: rebuild and audit every exported theorem.

Python standard library only. Run from any directory after installing the
pinned Lean toolchain and restoring dependencies with lake exe cache get.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import subprocess
import time

ROOT=Path(__file__).resolve().parents[1]
ALLOWED={'propext','Classical.choice','Quot.sound'}

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def uncomment(text):
    out=[]; i=0; depth=0
    while i<len(text):
        if text[i:i+2]=='/-': depth+=1; i+=2; continue
        if depth and text[i:i+2]=='-/': depth-=1; i+=2; continue
        if depth: i+=1; continue
        if text[i:i+2]=='--':
            end=text.find('\n',i)
            if end<0: break
            out.append('\n'); i=end+1; continue
        out.append(text[i]); i+=1
    assert depth==0
    return ''.join(out)

def audit(log,names):
    text=log.read_text(encoding='utf-8',errors='replace')
    deps={n:set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',v))
          for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",text): deps[n]=set()
    assert set(deps)==names,{'missing':sorted(names-set(deps)),'unexpected':sorted(set(deps)-names)}
    assert not {n:sorted(d-ALLOWED) for n,d in deps.items() if d-ALLOWED}
    return {n:sorted(d) for n,d in sorted(deps.items())}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'_verification')
    args=parser.parse_args()
    out=args.output.resolve()
    out.mkdir(parents=True,exist_ok=False)
    sources=json.loads((ROOT/'SOURCE_MANIFEST.json').read_text(encoding='utf-8'))
    for name,digest in sources.items(): assert sha(ROOT/name)==digest,name
    catalog=json.loads((ROOT/'THEOREM_CATALOG.json').read_text(encoding='utf-8'))
    names={x['name'] for x in catalog['theorems']}
    for f in [ROOT/'NoiseResponse.lean',ROOT/'Audit.lean',*sorted((ROOT/'NoiseResponse').glob('*.lean'))]:
        code=uncomment(f.read_text(encoding='utf-8'))
        assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',code),f
        assert not re.search(r'^\s*(?:constant|opaque)\b',code,re.M),f
        assert 'skipKernelTC' not in code,f
    stages=[]
    for name,command in [
        ('build',['lake','build']),
        ('axioms',['lake','env','lean','Audit.lean']),
        ('trust0',['lake','env','lean','Audit.lean','--trust=0','-M3000','-j2'])]:
        print(json.dumps({'stage':name,'state':'START'}),flush=True)
        start=time.perf_counter()
        log=out/(name+'.log')
        with log.open('xb') as f:
            p=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
        item=dict(stage=name,command=command,returncode=p.returncode,
                  seconds=time.perf_counter()-start,log_sha256=sha(log))
        stages.append(item)
        print(json.dumps(item),flush=True)
        if p.returncode:
            print(log.read_text(encoding='utf-8',errors='replace')[-6000:],flush=True)
            raise SystemExit(p.returncode)
    deps=audit(out/'axioms.log',names)
    assert audit(out/'trust0.log',names)==deps
    for name,digest in sources.items(): assert sha(ROOT/name)==digest,name
    version=subprocess.check_output(['lean','--version'],cwd=ROOT,text=True).strip()
    rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT/'.lake/packages/mathlib',text=True).strip()
    assert rev=='56a005855ea17e0b0958f73ec801ae140b0a1679'
    result=dict(status='PASS',completed_utc=datetime.now(timezone.utc).isoformat(),
                lean_version=version,mathlib_revision=rev,theorems=len(names),
                modules=catalog['module_count'],source_files=len(sources),additional_axioms=[],
                axiom_dependencies=deps,stages=stages,
                source_manifest_sha256=sha(ROOT/'SOURCE_MANIFEST.json'))
    (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='axiom_dependencies'},indent=2),flush=True)

if __name__=='__main__': main()
