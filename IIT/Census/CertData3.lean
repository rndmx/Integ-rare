/-
Census: kernel-checked certificates for the regions of a 3-set at pattern 0 whose profile is in
the orbit of `θ*` (profile `C_0 = {2}`, `C_1 = {0, 2}`, `C_2 = {0, 1}` and its relabellings;
rate `6.8307`, the lower bound for `I_3`).
-/
import IIT.Census.CertDataBase

namespace IIT
namespace Census

set_option maxRecDepth 100000

/-- Half-space certificate for the region of profile 0. -/
def cd_k3_0 : cd_Cert :=
  { C0 := [[false, false, true], [true, false, true], [true, true, false]],
    rows := [(cd_Row.min [0, 1, 0] [1, 0, 0], 2495269), (cd_Row.min [0, 1, 2] [0, 0, 0], 271087859), (cd_Row.min [0, 1, 2] [1, 0, 0], 49572684)],
    wF := 1073741824,
    v := [5108369354, 0, -2710878590, 0, 313387826, 0, -2710878590, 0, 5158274736, -1719424912, 0, 0, -1719424912, -1719424912, 0, 0, 5083416666, -1694472222, -1694472222, -1694472222, 0, 0, 0, 0] }

theorem cd_k3_0_ok : cd_check 3 cd_k3_0 68307 10000 = true := by decide +kernel

theorem cd_k3_0_cov : cd_Covered 3 68307 10000 cd_k3_0.C0 := Or.inl ⟨cd_k3_0, rfl, cd_k3_0_ok⟩

/-- Half-space certificate for the region of profile 1. -/
def cd_k3_1 : cd_Cert :=
  { C0 := [[false, true, false], [true, false, true], [true, true, false]],
    rows := [(cd_Row.min [0, 1, 2] [0, 0, 0], 268592589), (cd_Row.min [0, 1, 2] [0, 1, 0], 2495269), (cd_Row.min [0, 1, 2] [1, 0, 0], 52067953)],
    wF := 1073741824,
    v := [5108369348, 0, 313387812, 0, -2710878580, 0, -2710878580, 0, 5083416672, -1694472224, 0, 0, -1694472224, -1694472224, 0, 0, 5158274742, -1719424914, -1719424914, -1719424914, 0, 0, 0, 0] }

theorem cd_k3_1_ok : cd_check 3 cd_k3_1 68307 10000 = true := by decide +kernel

theorem cd_k3_1_cov : cd_Covered 3 68307 10000 cd_k3_1.C0 := Or.inl ⟨cd_k3_1, rfl, cd_k3_1_ok⟩

/-- Half-space certificate for the region of profile 2. -/
def cd_k3_2 : cd_Cert :=
  { C0 := [[false, true, true], [true, false, false], [true, true, false]],
    rows := [(cd_Row.min [0, 1, 2] [0, 0, 0], 268592589), (cd_Row.min [0, 1, 2] [0, 1, 0], 52067953), (cd_Row.min [0, 1, 2] [1, 0, 0], 2495269)],
    wF := 1073741824,
    v := [5083416672, 0, -1694472224, 0, -1694472224, 0, -1694472224, 0, 5108369348, 313387812, 0, 0, -2710878580, -2710878580, 0, 0, 5158274742, -1719424914, -1719424914, -1719424914, 0, 0, 0, 0] }

theorem cd_k3_2_ok : cd_check 3 cd_k3_2 68307 10000 = true := by decide +kernel

theorem cd_k3_2_cov : cd_Covered 3 68307 10000 cd_k3_2.C0 := Or.inl ⟨cd_k3_2, rfl, cd_k3_2_ok⟩

/-- Half-space certificate for the region of profile 3. -/
def cd_k3_3 : cd_Cert :=
  { C0 := [[false, true, true], [false, false, true], [true, true, false]],
    rows := [(cd_Row.min [0, 1, 2] [0, 0, 0], 268592589), (cd_Row.min [0, 1, 2] [0, 0, 1], 2495269), (cd_Row.min [0, 1, 2] [0, 1, 0], 52067953)],
    wF := 1073741824,
    v := [5158274742, 0, -1719424914, 0, -1719424914, 0, -1719424914, 0, 5108369348, -2710878580, 0, 0, 313387812, -2710878580, 0, 0, 5083416672, -1694472224, -1694472224, -1694472224, 0, 0, 0, 0] }

theorem cd_k3_3_ok : cd_check 3 cd_k3_3 68307 10000 = true := by decide +kernel

theorem cd_k3_3_cov : cd_Covered 3 68307 10000 cd_k3_3.C0 := Or.inl ⟨cd_k3_3, rfl, cd_k3_3_ok⟩

/-- Half-space certificate for the region of profile 4. -/
def cd_k3_4 : cd_Cert :=
  { C0 := [[false, true, true], [true, false, true], [true, false, false]],
    rows := [(cd_Row.min [0, 1, 2] [0, 0, 0], 268592589), (cd_Row.min [0, 1, 2] [0, 0, 1], 52067953), (cd_Row.min [0, 1, 2] [1, 0, 0], 2495269)],
    wF := 1073741824,
    v := [5083416672, 0, -1694472224, 0, -1694472224, 0, -1694472224, 0, 5158274742, -1719424914, 0, 0, -1719424914, -1719424914, 0, 0, 5108369348, 313387812, -2710878580, -2710878580, 0, 0, 0, 0] }

theorem cd_k3_4_ok : cd_check 3 cd_k3_4 68307 10000 = true := by decide +kernel

theorem cd_k3_4_cov : cd_Covered 3 68307 10000 cd_k3_4.C0 := Or.inl ⟨cd_k3_4, rfl, cd_k3_4_ok⟩

/-- Half-space certificate for the region of profile 5. -/
def cd_k3_5 : cd_Cert :=
  { C0 := [[false, true, true], [true, false, true], [false, true, false]],
    rows := [(cd_Row.min [0, 1, 2] [0, 0, 0], 268592589), (cd_Row.min [0, 1, 2] [0, 0, 1], 52067953), (cd_Row.min [0, 1, 2] [0, 1, 0], 2495269)],
    wF := 1073741824,
    v := [5158274742, 0, -1719424914, 0, -1719424914, 0, -1719424914, 0, 5083416672, -1694472224, 0, 0, -1694472224, -1694472224, 0, 0, 5108369348, -2710878580, 313387812, -2710878580, 0, 0, 0, 0] }

theorem cd_k3_5_ok : cd_check 3 cd_k3_5 68307 10000 = true := by decide +kernel

theorem cd_k3_5_cov : cd_Covered 3 68307 10000 cd_k3_5.C0 := Or.inl ⟨cd_k3_5, rfl, cd_k3_5_ok⟩

/-- The certified profiles. -/
def cd_k3_list : List (List (List Bool)) := [cd_k3_0.C0, cd_k3_1.C0, cd_k3_2.C0, cd_k3_3.C0, cd_k3_4.C0, cd_k3_5.C0]

/-- Every certified region is covered at rate `68307 / 10000`. -/
theorem cd_k3_covered : ∀ C ∈ cd_k3_list, cd_Covered 3 68307 10000 C := by
  intro C hC
  simp only [cd_k3_list, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cd_k3_0_cov
  · exact cd_k3_1_cov
  · exact cd_k3_2_cov
  · exact cd_k3_3_cov
  · exact cd_k3_4_cov
  · exact cd_k3_5_cov

end Census
end IIT
