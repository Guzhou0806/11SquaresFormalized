import ElevenSquare.Tasks.T01.Handoff.Inventory
namespace ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C08
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def part0 : List (ℕ × Group) := [
  (521, ⟨4, by decide⟩), (522, ⟨51, by decide⟩), (523, ⟨51, by decide⟩), (524, ⟨4, by decide⟩),
  (525, ⟨36, by decide⟩), (526, ⟨36, by decide⟩), (527, ⟨36, by decide⟩), (528, ⟨4, by decide⟩),
  (529, ⟨4, by decide⟩), (530, ⟨56, by decide⟩), (531, ⟨30, by decide⟩), (532, ⟨14, by decide⟩),
  (533, ⟨56, by decide⟩), (534, ⟨4, by decide⟩), (535, ⟨52, by decide⟩), (536, ⟨56, by decide⟩),
  (537, ⟨52, by decide⟩), (538, ⟨52, by decide⟩), (539, ⟨4, by decide⟩), (540, ⟨4, by decide⟩),
  (541, ⟨4, by decide⟩), (542, ⟨4, by decide⟩), (543, ⟨4, by decide⟩), (544, ⟨4, by decide⟩),
  (545, ⟨4, by decide⟩), (546, ⟨4, by decide⟩), (547, ⟨4, by decide⟩), (548, ⟨4, by decide⟩),
  (549, ⟨4, by decide⟩), (550, ⟨4, by decide⟩), (551, ⟨4, by decide⟩), (552, ⟨4, by decide⟩)
]
theorem part0_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part0 := by decide

def part1 : List (ℕ × Group) := [
  (553, ⟨4, by decide⟩), (554, ⟨43, by decide⟩), (555, ⟨4, by decide⟩), (556, ⟨4, by decide⟩),
  (557, ⟨4, by decide⟩), (558, ⟨4, by decide⟩), (559, ⟨4, by decide⟩), (560, ⟨4, by decide⟩),
  (561, ⟨4, by decide⟩), (562, ⟨4, by decide⟩), (563, ⟨5, by decide⟩), (564, ⟨4, by decide⟩),
  (565, ⟨4, by decide⟩), (566, ⟨4, by decide⟩), (567, ⟨53, by decide⟩), (568, ⟨4, by decide⟩),
  (569, ⟨42, by decide⟩), (570, ⟨4, by decide⟩), (571, ⟨4, by decide⟩), (572, ⟨4, by decide⟩),
  (573, ⟨4, by decide⟩), (574, ⟨4, by decide⟩), (575, ⟨4, by decide⟩), (576, ⟨4, by decide⟩),
  (577, ⟨4, by decide⟩), (578, ⟨4, by decide⟩), (579, ⟨4, by decide⟩), (580, ⟨4, by decide⟩),
  (581, ⟨43, by decide⟩), (582, ⟨43, by decide⟩), (583, ⟨4, by decide⟩), (584, ⟨5, by decide⟩)
]
theorem part1_valid :
    List.Forall (fun p => p.1 ∈ groupCases p.2) part1 := by decide

def assignments : List (ℕ × Group) := part0 ++ part1
theorem valid : List.Forall (fun p => p.1 ∈ groupCases p.2) assignments := by
  apply List.forall_iff_forall_mem.mpr
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact (List.forall_iff_forall_mem.mp part0_valid) p h
  · exact (List.forall_iff_forall_mem.mp part1_valid) p h

theorem keys_match : baselineArrayChunk8.toList = assignments.map Prod.fst := by decide

end ElevenSquare.Tasks.T01.Handoff.CoverageChunks.C08
