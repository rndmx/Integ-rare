/-
Census, B1 lower bound: the full-list 2-D certificate statements, glued from the chunks of `CertEX2DChk`.
-/
import IIT.Census.CertEX2DChk

set_option maxRecDepth 100000

namespace IIT
namespace Census

lemma ex2D_zip : exPCells.zip ex2DRecs = exPCells0.zip ex2DRecs0 ++ exPCells1.zip ex2DRecs1 ++ exPCells2.zip ex2DRecs2 ++ exPCells3.zip ex2DRecs3 ++ exPCells4.zip ex2DRecs4 ++ exPCells5.zip ex2DRecs5 ++ exPCells6.zip ex2DRecs6 ++ exPCells7.zip ex2DRecs7 ++ exPCells8.zip ex2DRecs8 ++ exPCells9.zip ex2DRecs9 ++ exPCells10.zip ex2DRecs10 := by
  simp only [exPCells, ex2DRecs, List.append_assoc]
  rw [List.zip_append ex2D_len0, List.zip_append ex2D_len1, List.zip_append ex2D_len2, List.zip_append ex2D_len3, List.zip_append ex2D_len4, List.zip_append ex2D_len5, List.zip_append ex2D_len6, List.zip_append ex2D_len7, List.zip_append ex2D_len8, List.zip_append ex2D_len9]

theorem ex2D_ok : (exPCells.zip ex2DRecs).all (fun p => ex2DOK p.1 p.2) = true := by
  rw [ex2D_zip]; simp only [List.all_append, ex2D_ok0, ex2D_ok1, ex2D_ok2, ex2D_ok3, ex2D_ok4, ex2D_ok5, ex2D_ok6, ex2D_ok7, ex2D_ok8, ex2D_ok9, ex2D_ok10, Bool.and_self]

theorem exS_lo : exESlo ≤ ((exPCells.zip ex2DRecs).map fun p => p.1.a * p.2.sl).sum := by
  rw [ex2D_zip]; simp only [List.map_append, List.sum_append, ex2D_sl0, ex2D_sl1, ex2D_sl2, ex2D_sl3, ex2D_sl4, ex2D_sl5, ex2D_sl6, ex2D_sl7, ex2D_sl8, ex2D_sl9, ex2D_sl10]
  unfold exESlo; norm_num

theorem exV_up : ((exPCells.zip ex2DRecs).map fun p => p.1.a * p.2.vu).sum ≤ exEVup := by
  rw [ex2D_zip]; simp only [List.map_append, List.sum_append, ex2D_vu0, ex2D_vu1, ex2D_vu2, ex2D_vu3, ex2D_vu4, ex2D_vu5, ex2D_vu6, ex2D_vu7, ex2D_vu8, ex2D_vu9, ex2D_vu10]
  unfold exEVup; norm_num

theorem exM_lo : exEMlo ≤ ((exPCells.zip ex2DRecs).map fun p => p.1.a * p.2.ml).sum := by
  rw [ex2D_zip]; simp only [List.map_append, List.sum_append, ex2D_ml0, ex2D_ml1, ex2D_ml2, ex2D_ml3, ex2D_ml4, ex2D_ml5, ex2D_ml6, ex2D_ml7, ex2D_ml8, ex2D_ml9, ex2D_ml10]
  unfold exEMlo; norm_num

theorem exD_lo : exEDlo ≤ ((exPCells.zip ex2DRecs).map fun p => p.1.a * p.2.dl).sum := by
  rw [ex2D_zip]; simp only [List.map_append, List.sum_append, ex2D_dl0, ex2D_dl1, ex2D_dl2, ex2D_dl3, ex2D_dl4, ex2D_dl5, ex2D_dl6, ex2D_dl7, ex2D_dl8, ex2D_dl9, ex2D_dl10]
  unfold exEDlo; norm_num

theorem ex2DRecs_len : ex2DRecs.length = 4159 := by
  have h := congrArg List.length ex2D_zip
  rw [List.length_zip] at h
  have hp : exPCells.length = 4159 := exPCells_len
  simp only [ex2DRecs, List.length_append] at *
  simp only [exPCells, List.length_append] at hp
  simp only [ex2D_len0, ex2D_len1, ex2D_len2, ex2D_len3, ex2D_len4, ex2D_len5, ex2D_len6, ex2D_len7, ex2D_len8, ex2D_len9, ex2D_len10] at hp
  omega

end Census
end IIT
