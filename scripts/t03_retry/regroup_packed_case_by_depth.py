"""Keep the exact source plan; group independent modules at each dependency depth."""
from pathlib import Path
import argparse,collections,ctypes,functools,json,zipfile
from retry_paths import kit_paths, low_priority_single_core
ap=argparse.ArgumentParser();ap.add_argument('--case',type=int,required=True)
ap.add_argument('--preserve-original-module',action='append',default=[])
ap.add_argument('--kit',required=True);ap.add_argument('--archive',required=True)
args=ap.parse_args();case=args.case
_,E,_=kit_paths(args.kit)
assert case in {r['case'] for r in json.loads((E/'forward-workload-inventory.json').read_text())['records']}
low_priority_single_core()
path=E/f'case{case}-packed-compilation-plan.json';p=json.loads(path.read_text())
backup=E/f'case{case}-packed-compilation-greedy-plan.json'
if p.get('grouped_by_dependency_depth'):
 assert args.preserve_original_module and not p.get('preserved_original_modules')
 assert not (E/f'case{case}-packed-namespaced-publication.json').exists()
 previous=E/f'case{case}-packed-compilation-depth-before-passthrough-plan.json'
 assert not previous.exists();previous.write_bytes(path.read_bytes())
 p=json.loads(backup.read_text())
else:
 assert not backup.exists();backup.write_bytes(path.read_bytes())
selected={m for g in p['groups'] for m in g}
preserved=set(args.preserve_original_module)
assert preserved<=selected and p['original_task']['modules'][0] not in preserved
selected-=preserved
@functools.lru_cache(maxsize=None)
def ancestors(module):
 result=set()
 for dep in p['graph'][module]:result.add(dep);result.update(ancestors(dep))
 return frozenset(result)
for module in preserved:
 assert not ancestors(module)&selected,('Original helper must not import a grouped ancestor',module)
depth={};levels=collections.defaultdict(list)
for m,deps in p['graph'].items():
 if m in selected:depth[m]=1+max((depth[d] for d in deps if d in selected),default=0);levels[depth[m]].append(m)
assert set(depth)==selected
prefix=p['root_module'].rsplit('.',1)[0];groups=[]
archive=Path(args.archive).resolve();assert archive.is_file()
with zipfile.ZipFile(archive) as z:
 for level in sorted(levels):
  group=[];size=0
  for m in levels[level]:
   n=z.getinfo('project/'+m.replace('.','/')+'.lean').file_size
   if group and (len(group)>=64 or size+n>8*1024*1024):groups.append(group);group=[];size=0
   group.append(m);size+=n
  if group:groups.append(group)
mapping={m:prefix+f'.Chunk{i:03d}' for i,g in enumerate(groups) for m in g}
external={d for deps in p['chunk_imports'].values() for d in deps if not (d=='ElevenSquare' or d.startswith('ElevenSquare.'))}
imports={}
for i,g in enumerate(groups):
 own=prefix+f'.Chunk{i:03d}';deps=set(external)|{'ElevenSquare.Tasks.T03.KernelBoolRefl'}
 for m in g:deps.update(mapping.get(d,d) for d in p['graph'][m] if mapping.get(d,d)!=own)
 imports[own]=sorted(deps)
p.update(groups=groups,chunk_imports=imports,root_module=mapping[p['original_task']['modules'][0]],
         grouped_by_dependency_depth=True,dependency_depths=len(levels),maximum_parallel_module_width=max(map(len,levels.values())),
         original_greedy_plan=backup.name,rule='Group independent cold declarations at each dependency depth; warm frontier has no grouped ancestor.')
if preserved:
 p.update(preserved_original_modules=sorted(preserved),grouped_modules=len(selected),
          original_helper_imports_may_require_normal_checker_validation=True,
          rule='Group independent generated declarations; retain exact original helper sources with no grouped ancestors. The supplied checker validates any cold original helper before reuse.')
path.write_text(json.dumps(p,indent=2)+'\n')
print(json.dumps(dict(status='EXACT_SOURCE_DEPTH_GROUPING_PLAN',case=case,modules=len(selected),groups=len(groups),
                     dependency_depths=len(levels),maximum_parallel_module_width=max(map(len,levels.values())),root_module=p['root_module'])),flush=True)
