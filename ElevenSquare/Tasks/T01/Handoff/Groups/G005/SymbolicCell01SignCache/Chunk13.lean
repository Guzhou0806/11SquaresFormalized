import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk13
open ElevenSquare.Tasks.T01.Handoff.PlanAPI

def polynomial156 : Quartic := ⟨1211324591, -1081785010, -1211324591, 0, 0⟩

theorem sign156 : polynomial156.BernsteinNonnegCheck (91/256) (25/64) := by
  norm_num [polynomial156, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry156 : CachedQuarticSign :=
  ⟨polynomial156, (91/256), (25/64),
    false, .leaf⟩

theorem entry156_checked : entry156.Check := by
  change polynomial156.BernsteinNonnegCheck (91/256) (25/64)
  exact sign156

def polynomial157 : Quartic := ⟨12159645579687084446761952560729782413443, 3615985559016862190206545906315288297330, -10969740047710825530400000000000000000000, -37527908118887206097793454093684711702670, 55327916173753457885238047439270217586557⟩

theorem sign157 : polynomial157.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial157, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry157 : CachedQuarticSign :=
  ⟨polynomial157, 0, 1,
    false, .leaf⟩

theorem entry157_checked : entry157.Check := by
  change polynomial157.BernsteinNonnegCheck 0 1
  exact sign157

def polynomial158 : Quartic := ⟨1217607363814015036754415076951047264522844943, -3979369736648324312486071338164668230170783730, 2974931481248300743674020000000000000000000000, 1454296228390416502702728661835331769829216270, -1609833954341655561973435076951047264522844943⟩

theorem sign158 : polynomial158.BernsteinNonnegCheck (3/4) 1 := by
  norm_num [polynomial158, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry158 : CachedQuarticSign :=
  ⟨polynomial158, (3/4), 1,
    false, .leaf⟩

theorem entry158_checked : entry158.Check := by
  change polynomial158.BernsteinNonnegCheck (3/4) 1
  exact sign158

def polynomial159 : Quartic := ⟨122994906893148787183778446448016675, 2345705103380949227878652692610035329, 1313567756903922035900978270520975158, -2993304588179389227878652692610035329, -2264452568202351212816221553551983325⟩

theorem sign159 : polynomial159.BernsteinNonnegCheck 0 (1/64) := by
  norm_num [polynomial159, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry159 : CachedQuarticSign :=
  ⟨polynomial159, 0, (1/64),
    false, .leaf⟩

theorem entry159_checked : entry159.Check := by
  change polynomial159.BernsteinNonnegCheck 0 (1/64)
  exact sign159

def polynomial160 : Quartic := ⟨123900000674693873813352416576909416785663010086283613, -259246261888617894163466654432608000000000000000000000, -139344606815327698577325307935762583214336989913716387, 0, 0⟩

theorem sign160 : polynomial160.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial160, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry160 : CachedQuarticSign :=
  ⟨polynomial160, (21/64), (91/256),
    false, .leaf⟩

theorem entry160_checked : entry160.Check := by
  change polynomial160.BernsteinNonnegCheck (21/64) (91/256)
  exact sign160

def polynomial161 : Quartic := ⟨12465658373606293390463940, 10948426590329484948336767533, 3819996180000000000000000000000, -7629051573409670515051663232467, 3819983714341626393706609536060⟩

theorem sign161 : polynomial161.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial161, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry161 : CachedQuarticSign :=
  ⟨polynomial161, 0, 1,
    false, .leaf⟩

theorem entry161_checked : entry161.Check := by
  change polynomial161.BernsteinNonnegCheck 0 1
  exact sign161

def polynomial162 : Quartic := ⟨128113438418187309902284084984080288109093, 3394801424010472640117000000000000000000000, -3356548953789829490534715915015919711890907, 0, 0⟩

theorem sign162 : polynomial162.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial162, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry162 : CachedQuarticSign :=
  ⟨polynomial162, 0, 1,
    false, .leaf⟩

theorem entry162_checked : entry162.Check := by
  change polynomial162.BernsteinNonnegCheck 0 1
  exact sign162

def polynomial163 : Quartic := ⟨1290197938698508769078416756393136472755, 41867768230105440280960160199746089404158, 79892939654215919170400000000000000000000, -58693991815466620730239839800253910595842, -22831728739927940014678416756393136472755⟩

theorem sign163 : polynomial163.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial163, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry163 : CachedQuarticSign :=
  ⟨polynomial163, 0, 1,
    false, .leaf⟩

theorem entry163_checked : entry163.Check := by
  change polynomial163.BernsteinNonnegCheck 0 1
  exact sign163

def polynomial164 : Quartic := ⟨132741062333541981121096000000, 271525087292028299883516527423, 3554510235332916037757808000000, -271525087292028299883516527423, -3687251297666458018878904000000⟩

theorem sign164 : polynomial164.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial164, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry164 : CachedQuarticSign :=
  ⟨polynomial164, 0, 1,
    false, .leaf⟩

theorem entry164_checked : entry164.Check := by
  change polynomial164.BernsteinNonnegCheck 0 1
  exact sign164

def polynomial165 : Quartic := ⟨13297560534724836901681660950000, 82348369789441601408007272098129, 74602191664400000000000000000000, -200589630210558398591992727901871, 195037831129675163098318339050000⟩

theorem sign165 : polynomial165.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial165, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry165 : CachedQuarticSign :=
  ⟨polynomial165, 0, 1,
    false, .leaf⟩

theorem entry165_checked : entry165.Check := by
  change polynomial165.BernsteinNonnegCheck 0 1
  exact sign165

def polynomial166 : Quartic := ⟨1337625260640591112945320080518483487980, -6279219222685588382115204857675724077489, 12646731342100003820000000000000000000000, -8224870612912252502115204857675724077489, -1337627935913923172945320080518483487980⟩

theorem sign166 : polynomial166.BernsteinNonnegCheck (21/64) (91/256) := by
  norm_num [polynomial166, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry166 : CachedQuarticSign :=
  ⟨polynomial166, (21/64), (91/256),
    false, .leaf⟩

theorem entry166_checked : entry166.Check := by
  change polynomial166.BernsteinNonnegCheck (21/64) (91/256)
  exact sign166

def polynomial167 : Quartic := ⟨134097772871333403345243503059597348985964246332905291, 654204621013439175643785420324200000000000000000000000, -634344717402425399437693018561722651014035753667094709, 0, 0⟩

theorem sign167 : polynomial167.BernsteinNonnegCheck 0 1 := by
  norm_num [polynomial167, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

def entry167 : CachedQuarticSign :=
  ⟨polynomial167, 0, 1,
    false, .leaf⟩

theorem entry167_checked : entry167.Check := by
  change polynomial167.BernsteinNonnegCheck 0 1
  exact sign167

end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01SignCache.Chunk13
