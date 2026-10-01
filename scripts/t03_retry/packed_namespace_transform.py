"""Rename generated private constants without redirecting warm declarations.

Generated input is restricted to its observed namespace/section/def/theorem/open
grammar. The original task's exact certificate type is bridged separately.
"""
import functools, re

NS=re.compile(r'^namespace ([A-Za-z_][A-Za-z_0-9.]*)\s*$')
SEC=re.compile(r'^(?:noncomputable )?section(?:\s.*)?$')
END=re.compile(r'^end(?:\s+([A-Za-z_][A-Za-z_0-9.]*))?\s*$')
DECL=re.compile(r'^(?:noncomputable\s+)?(def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)\b')
TOKENS=re.compile(r'"(?:[^"\\]|\\.)*"|--[^\n]*|\b[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+\b')

class Renamer:
 def __init__(self, sources, suffix='PackedCase1646'):
  self.suffix=suffix;self.namespaces=set();self.declarations=set()
  for module,text in sources():
   assert '/-' not in text,('Unsupported block comment',module)
   ns='';stack=[]
   for line in text.splitlines():
    if m:=NS.fullmatch(line):
     full=ns+'.'+m[1] if ns else m[1];stack.append(('namespace',ns,m[1]));ns=full;self.namespaces.add(ns)
    elif SEC.fullmatch(line):stack.append(('section',ns,''))
    elif m:=END.fullmatch(line):
     assert stack,(module,line);kind,previous,short=stack.pop()
     assert m[1] is None or kind=='namespace' and m[1]==short,(module,line,kind,short)
     if kind=='namespace':ns=previous
    elif m:=DECL.match(line):
     name=ns+'.'+m[2];assert name not in self.declarations,('Duplicate generated declaration',name)
     self.declarations.add(name)
    elif re.fullmatch(r'#print axioms [A-Za-z_][A-Za-z_0-9.]*',line):
     pass
    elif line and not line[0].isspace() and not line.startswith(('import ','set_option ','open ','--')):
     raise AssertionError(('Unsupported generated command',module,line[:100]))
   assert not stack,(module,stack)
  self.roots={n for n in self.namespaces if not any('.'.join(n.split('.')[:i]) in self.namespaces for i in range(1,len(n.split('.'))))}
  self.mapping={n:self.rename_namespace(n) for n in self.namespaces}
  self.changed_references=0

 @functools.lru_cache(maxsize=None)
 def rename_namespace(self,n):
  parts=n.split('.')
  for i in range(1,len(parts)+1):
   prefix='.'.join(parts[:i])
   if prefix in self.roots:return prefix+'.'+self.suffix+('.'+'.'.join(parts[i:]) if i<len(parts) else '')
  raise AssertionError(('Namespace outside copied roots',n))

 @functools.lru_cache(maxsize=None)
 def resolve(self, token, ns, namespace=False):
  if not token[0].isupper():return token
  candidates=[token] if token.startswith('ElevenSquare.') else ['.'.join(ns.split('.')[:i]+[token]) for i in range(len(ns.split('.')),-1,-1)]
  known=self.namespaces if namespace else self.declarations
  for full in candidates:
   if namespace:
    if full in known:return self.rename_namespace(full)
    continue
   parts=full.split('.')
   for i in range(len(parts),0,-1):
    prefix='.'.join(parts[:i])
    if prefix in known:
     parent,short=prefix.rsplit('.',1)
     return self.rename_namespace(parent)+'.'+short+('.'+'.'.join(parts[i:]) if i<len(parts) else '')
  return token

 def transform(self,text):
  ns='';stack=[];result=[]
  for line in text.splitlines(keepends=True):
   clean=line.rstrip('\n')
   if m:=NS.fullmatch(clean):
    previous=ns;full=ns+'.'+m[1] if ns else m[1]
    new=self.rename_namespace(full)
    short=new if not ns else new.removeprefix(self.rename_namespace(ns)+'.')
    assert ns=='' or new.startswith(self.rename_namespace(ns)+'.'),(ns,new)
    result.append('namespace '+short+'\n');stack.append(('namespace',previous,short));ns=full
   elif SEC.fullmatch(clean):stack.append(('section',ns,''));result.append(line)
   elif m:=END.fullmatch(clean):
    kind,previous,short=stack.pop()
    result.append('end'+(' '+short if m[1] else '')+'\n')
    if kind=='namespace':ns=previous
   elif clean.startswith('open '):
    # All generated opens are plain namespace lists, without hiding/renaming.
    terms=clean[5:].split();assert all(re.fullmatch('[A-Za-z_][A-Za-z_0-9.]*',t) for t in terms),clean
    result.append('open '+' '.join(self.resolve(t,ns,True) for t in terms)+'\n')
   else:
    def replace(m):
     token=m[0]
     if token.startswith(('"','--')):return token
     out=self.resolve(token,ns)
     if out!=token:self.changed_references+=1
     return out
    result.append(TOKENS.sub(replace,line))
  assert not stack
  return ''.join(result)
