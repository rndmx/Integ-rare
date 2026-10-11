/-
Census: the partition `θ*` of `TripleLower` in the certificate encoding.

Along the ordering `(a, b, c)` the profile of `tl_thetaStar a b c` is the table `cd_Cstar`
(`cd_star_profile`), which is the first certified profile of `CertData3`; every relabelling of
`cd_Cstar` by a permutation of the three units is one of the six certified profiles of `CertData3`
(`cd_star_relabel`), so the region of `θ*` read along any ordering of `{a, b, c}` is covered at rate
`6.8307`.
-/
import IIT.Census.TripleLower
import IIT.Census.CertDataPoint
import IIT.Census.CertData3

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The ordering `(a, b, c)` of a triple. -/
def cd_ord3 (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ Fin N :=
  ⟨![a, b, c], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

@[simp] lemma cd_ord3_apply (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i : Fin 3) :
    cd_ord3 a b c hab hac hbc i = ![a, b, c] i := rfl

lemma cd_ord3_onto (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : Fin N) :
    x ∈ ({a, b, c} : Finset (Fin N)) ↔ ∃ i, cd_ord3 a b c hab hac hbc i = x := by
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

/-- **The profile of `θ*` along `(a, b, c)`.** -/
theorem cd_star_profile (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i j : Fin 3) :
    cd_ord3 a b c hab hac hbc j ∈ profile (tl_thetaStar a b c hab hac hbc) (cd_ord3 a b c hab hac hbc i)
      ↔ cd_at cd_Cstar i j = true := by
  have ha := tl_profile_a hab hac hbc
  have hb := tl_profile_b hab hac hbc
  have hc := tl_profile_c hab hac hbc
  fin_cases i <;> fin_cases j <;>
    simp [ha, hb, hc, cd_at, cd_Cstar, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]

lemma cd_Cstar_eq : cd_k3_0.C0 = cd_Cstar := rfl

/-- The relabellings of `cd_Cstar` are the certified profiles of `CertData3`. -/
theorem cd_star_relabel (σ : Equiv.Perm (Fin 3)) :
    ∃ C ∈ cd_k3_list, ∀ i j : Fin 3, cd_at C i j = cd_at cd_Cstar (σ i) (σ j) := by
  revert σ
  decide

end Census
end IIT
