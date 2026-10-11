/-
Census: kernel-checked certificates for the regions of a 2-set at pattern 0, one per
unit-permutation orbit of realized profiles (Theorem E, rate `2560/61 (1 - 10^-6)`).
-/
import IIT.Census.CertDataBase

namespace IIT
namespace Census

set_option maxRecDepth 100000

/-- Gordan certificate for the region of profile 0. -/
def cd_k2_0 : cd_GCert :=
  { C0 := [[false, true], [true, false]],
    r0 := cd_Row.min [0, 1] [0, 1], w0 := 1,
    rows := [(cd_Row.min [0, 1] [1, 0], 1)] }

theorem cd_k2_0_ok : cd_checkG 2 cd_k2_0 = true := by decide +kernel

theorem cd_k2_0_cov : cd_Covered 2 7999992 190625 cd_k2_0.C0 := Or.inr ⟨cd_k2_0, rfl, cd_k2_0_ok⟩

/-- Half-space certificate for the region of profile 1. -/
def cd_k2_1 : cd_Cert :=
  { C0 := [[false, true], [false, false]],
    rows := [(cd_Row.min [0, 1] [1, 0], 1)],
    wF := 2,
    v := [2, 0, -2, 0, 2, -2, 0, 0] }

theorem cd_k2_1_ok : cd_check 2 cd_k2_1 7999992 190625 = true := by decide +kernel

theorem cd_k2_1_cov : cd_Covered 2 7999992 190625 cd_k2_1.C0 := Or.inl ⟨cd_k2_1, rfl, cd_k2_1_ok⟩

/-- The certified profiles. -/
def cd_k2_list : List (List (List Bool)) := [cd_k2_0.C0, cd_k2_1.C0]

/-- Every certified region is covered at rate `7999992 / 190625`. -/
theorem cd_k2_covered : ∀ C ∈ cd_k2_list, cd_Covered 2 7999992 190625 C := by
  intro C hC
  simp only [cd_k2_list, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl
  · exact cd_k2_0_cov
  · exact cd_k2_1_cov

end Census
end IIT
