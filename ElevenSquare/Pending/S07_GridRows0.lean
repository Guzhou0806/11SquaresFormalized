import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks0
import ElevenSquare.Pending.S07_GridVertexChecks1
namespace ElevenSquare.Pending.GridDistance

theorem row_check0 : rowCheck rationalRow0 gridRow0 = true := by
  simp only [rowCheck, rationalRow0, gridRow0, zipCheck, vertex_check0, vertex_check1, vertex_check2, vertex_check3, Bool.true_and]

theorem row_check1 : rowCheck rationalRow1 gridRow1 = true := by
  simp only [rowCheck, rationalRow1, gridRow1, zipCheck, vertex_check1, vertex_check4, vertex_check2, Bool.true_and]

theorem row_check2 : rowCheck rationalRow2 gridRow2 = true := by
  simp only [rowCheck, rationalRow2, gridRow2, zipCheck, vertex_check5, vertex_check6, vertex_check7, vertex_check8, Bool.true_and]

theorem row_check3 : rowCheck rationalRow3 gridRow3 = true := by
  simp only [rowCheck, rationalRow3, gridRow3, zipCheck, vertex_check6, vertex_check9, vertex_check0, vertex_check3, vertex_check10, vertex_check7, Bool.true_and]

theorem row_check4 : rowCheck rationalRow4 gridRow4 = true := by
  simp only [rowCheck, rationalRow4, gridRow4, zipCheck, vertex_check11, vertex_check12, vertex_check13, vertex_check14, Bool.true_and]

theorem row_check5 : rowCheck rationalRow5 gridRow5 = true := by
  simp only [rowCheck, rationalRow5, gridRow5, zipCheck, vertex_check12, vertex_check15, vertex_check13, Bool.true_and]

theorem row_check6 : rowCheck rationalRow6 gridRow6 = true := by
  simp only [rowCheck, rationalRow6, gridRow6, zipCheck, vertex_check16, vertex_check17, vertex_check11, vertex_check14, Bool.true_and]

theorem row_check7 : rowCheck rationalRow7 gridRow7 = true := by
  simp only [rowCheck, rationalRow7, gridRow7, zipCheck, vertex_check14, vertex_check13, vertex_check18, vertex_check8, vertex_check7, vertex_check19, Bool.true_and]

theorem row_check8 : rowCheck rationalRow8 gridRow8 = true := by
  simp only [rowCheck, rationalRow8, gridRow8, zipCheck, vertex_check13, vertex_check15, vertex_check20, vertex_check18, Bool.true_and]

theorem row_check9 : rowCheck rationalRow9 gridRow9 = true := by
  simp only [rowCheck, rationalRow9, gridRow9, zipCheck, vertex_check21, vertex_check16, vertex_check14, vertex_check19, Bool.true_and]

theorem row_check10 : rowCheck rationalRow10 gridRow10 = true := by
  simp only [rowCheck, rationalRow10, gridRow10, zipCheck, vertex_check10, vertex_check22, vertex_check19, vertex_check7, Bool.true_and]

theorem row_check11 : rowCheck rationalRow11 gridRow11 = true := by
  simp only [rowCheck, rationalRow11, gridRow11, zipCheck, vertex_check22, vertex_check21, vertex_check19, Bool.true_and]

theorem row_check12 : rowCheck rationalRow12 gridRow12 = true := by
  simp only [rowCheck, rationalRow12, gridRow12, zipCheck, vertex_check23, vertex_check24, vertex_check25, Bool.true_and]

theorem row_check13 : rowCheck rationalRow13 gridRow13 = true := by
  simp only [rowCheck, rationalRow13, gridRow13, zipCheck, vertex_check24, vertex_check26, vertex_check27, vertex_check28, vertex_check25, Bool.true_and]

theorem row_check14 : rowCheck rationalRow14 gridRow14 = true := by
  simp only [rowCheck, rationalRow14, gridRow14, zipCheck, vertex_check26, vertex_check29, vertex_check27, Bool.true_and]

theorem row_check15 : rowCheck rationalRow15 gridRow15 = true := by
  simp only [rowCheck, rationalRow15, gridRow15, zipCheck, vertex_check1, vertex_check0, vertex_check30, Bool.true_and]

theorem aligned_chunk0 : ArrayAligned Row recordedOverlayVerticesChunk0 gridChunk0 := by
  have heq : recordedOverlayVerticesChunk0 = rationalChunk0 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow0, rationalRow1, rationalRow2, rationalRow3, rationalRow4, rationalRow5, rationalRow6, rationalRow7, rationalRow8, rationalRow9, rationalRow10, rationalRow11, rationalRow12, rationalRow13, rationalRow14, rationalRow15] [gridRow0, gridRow1, gridRow2, gridRow3, gridRow4, gridRow5, gridRow6, gridRow7, gridRow8, gridRow9, gridRow10, gridRow11, gridRow12, gridRow13, gridRow14, gridRow15]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow0 gridRow0 row_check0) (List.Forall₂.cons (rowCheck_sound rationalRow1 gridRow1 row_check1) (List.Forall₂.cons (rowCheck_sound rationalRow2 gridRow2 row_check2) (List.Forall₂.cons (rowCheck_sound rationalRow3 gridRow3 row_check3) (List.Forall₂.cons (rowCheck_sound rationalRow4 gridRow4 row_check4) (List.Forall₂.cons (rowCheck_sound rationalRow5 gridRow5 row_check5) (List.Forall₂.cons (rowCheck_sound rationalRow6 gridRow6 row_check6) (List.Forall₂.cons (rowCheck_sound rationalRow7 gridRow7 row_check7) (List.Forall₂.cons (rowCheck_sound rationalRow8 gridRow8 row_check8) (List.Forall₂.cons (rowCheck_sound rationalRow9 gridRow9 row_check9) (List.Forall₂.cons (rowCheck_sound rationalRow10 gridRow10 row_check10) (List.Forall₂.cons (rowCheck_sound rationalRow11 gridRow11 row_check11) (List.Forall₂.cons (rowCheck_sound rationalRow12 gridRow12 row_check12) (List.Forall₂.cons (rowCheck_sound rationalRow13 gridRow13 row_check13) (List.Forall₂.cons (rowCheck_sound rationalRow14 gridRow14 row_check14) (List.Forall₂.cons (rowCheck_sound rationalRow15 gridRow15 row_check15) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk0
