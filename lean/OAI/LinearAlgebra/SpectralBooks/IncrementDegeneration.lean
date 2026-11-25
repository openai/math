import OAI.LinearAlgebra.SpectralBooks.Increment
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Local diagonal specializations for the common-label increment

After coefficient extraction, the surviving coordinates satisfy an integer
equation. Two successive local rescalings, with Laurent powers allowed at
the individual sites, give polynomial curves on this support. Their final
value at zero is the coefficient of the product of two independent diagonals.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Polynomial

section

private theorem exists_weight_polynomial (F : Type*) [Field F]
    (S T : Prop) [Decidable S] [Decidable T] (e : ℤ) (hne : S → 0 ≤ e)
    (hz : S ∧ e = 0 ↔ T) :
    ∃ P : F[X], (∀ t : F, t ≠ 0 → P.eval t = (if S then 1 else 0) * t ^ e) ∧
      P.eval 0 = if T then 1 else 0 := by
  by_cases hS : S
  · refine ⟨X ^ e.toNat, ?_, ?_⟩
    · intro t _
      simp only [eval_X_pow, hS, ite_true, one_mul]
      rw [← zpow_natCast, Int.toNat_of_nonneg (hne hS)]
    · by_cases he : e = 0
      · simp [he, hz.mp ⟨hS, he⟩]
      · have he' : e.toNat ≠ 0 := by have := hne hS; omega
        have hT : ¬T := fun h ↦ he (hz.mpr h).2
        simp [zero_pow he', hT]
  · have hT : ¬T := fun h ↦ hS (hz.mpr h).1
    exact ⟨0, by simp [hS], by simp [hT]⟩

private theorem zpow_sum_eq_prod {F ι : Type*} [Field F] (t : F) (ht : t ≠ 0)
    (s : Finset ι) (w : ι → ℤ) : t ^ (∑ j ∈ s, w j) = ∏ j ∈ s, t ^ w j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [hj, zpow_add₀ ht, ih]

/-- The first polynomial path uses the local rescalings at the new site, at
site 1 and at the remaining sites, respectively. Its fiber at zero enforces
`g = h` and the averaging equation on the old intersection. -/
theorem firstDiagonalSpecialization (F : Type*) [Field F] {ι : Type*} [Fintype ι]
    (g h a : ℤ) (v : ι → ℤ) :
    ∃ P : F[X],
      (∀ t : F, t ≠ 0 → P.eval t =
        (if g = h + ∑ j, v j - Fintype.card ι * a then 1 else 0) *
          (t ^ (g ^ 2) * t ^ (-h ^ 2 + 2 * h * (Fintype.card ι * a)) *
            ∏ j, t ^ (-(2 * h * v j)))) ∧
      P.eval 0 = if g = h ∧ ∑ j, v j = Fintype.card ι * a then 1 else 0 := by
  let e := g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * a)) + ∑ j, -(2 * h * v j)
  have hweight (hs : g = h + ∑ j, v j - Fintype.card ι * a) : e = (g - h) ^ 2 :=
    firstWeight_eq_sq g h a v hs
  obtain ⟨P, hP, hP₀⟩ := exists_weight_polynomial F
    (g = h + ∑ j, v j - Fintype.card ι * a)
    (g = h ∧ ∑ j, v j = Fintype.card ι * a) e
    (fun hs ↦ hweight hs ▸ sq_nonneg _) (by
      constructor
      · rintro ⟨hs, he⟩
        obtain heq := (firstWeight_eq_zero_iff g h a v hs).mp he
        exact ⟨heq, by linarith⟩
      · rintro ⟨heq, hc⟩
        have hs : g = h + ∑ j, v j - Fintype.card ι * a := by rw [hc, add_sub_cancel_right, heq]
        exact ⟨hs, (firstWeight_eq_zero_iff g h a v hs).mpr heq⟩)
  refine ⟨P, fun t ht ↦ ?_, hP₀⟩
  rw [hP t ht]
  simp only [e, zpow_add₀ ht, zpow_sum_eq_prod t ht]

/-- On the first special fiber, a second local rescaling specializes to the
product of the common `h`-label diagonal and the independent common `a`-label
diagonal. Each listed power is local to a single site. -/
theorem secondDiagonalSpecialization (F : Type*) [Field F] {ι : Type*} [Fintype ι]
    (g h a : ℤ) (v : ι → ℤ) [Decidable (∀ j, v j = a)] :
    ∃ P : F[X],
      (∀ t : F, t ≠ 0 → P.eval t =
        (if g = h ∧ ∑ j, v j = Fintype.card ι * a then 1 else 0) *
          (t ^ (-(Fintype.card ι : ℤ) * a ^ 2) * ∏ j, t ^ (v j ^ 2))) ∧
      P.eval 0 = if g = h ∧ ∀ j, v j = a then 1 else 0 := by
  let e := -(Fintype.card ι : ℤ) * a ^ 2 + ∑ j, v j ^ 2
  have hweight (hc : ∑ j, v j = Fintype.card ι * a) : e = ∑ j, (v j - a) ^ 2 := by
    rw [← secondWeight_eq_sum_sq a v hc]
    dsimp [e]
    ring
  obtain ⟨P, hP, hP₀⟩ := exists_weight_polynomial F
    (g = h ∧ ∑ j, v j = Fintype.card ι * a) (g = h ∧ ∀ j, v j = a) e
    (fun hs ↦ hweight hs.2 ▸ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)) (by
      constructor
      · rintro ⟨⟨hg, hc⟩, he⟩
        refine ⟨hg, ?_⟩
        rw [hweight hc, Finset.sum_sq_eq_zero_iff] at he
        simpa [sub_eq_zero] using he
      · rintro ⟨hg, hv⟩
        have hc : ∑ j, v j = Fintype.card ι * a := by simp [hv]
        exact ⟨⟨hg, hc⟩, by simp [hweight hc, hv]⟩)
  refine ⟨P, fun t ht ↦ ?_, hP₀⟩
  rw [hP t ht]
  simp only [e, zpow_add₀ ht, zpow_sum_eq_prod t ht]

end

end SpectralBooks
end LinearAlgebra
end OAI
