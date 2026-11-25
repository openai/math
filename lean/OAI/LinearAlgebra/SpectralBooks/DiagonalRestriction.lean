import OAI.LinearAlgebra.SpectralBooks.IncrementDegeneration
import OAI.LinearAlgebra.SpectralBooks.SourceRestrictions
import OAI.LinearAlgebra.SpectralBooks.ZariskiCurve

/-! # Degenerating to the product of independent diagonals

In the coordinate format for the increment lemma, the old label `h` is
copied to the new site and an independent label `a` is shared among the
intersection sites. The construction works over every infinite field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Polynomial

section

private theorem specialize_local_scalings {F : Type*} [Field F] [Infinite F]
    {q k m L : ℕ} {S T : IncrementCoordinate q k m → F}
    (u : F → Fin q → Fin q → F) (b : F → Fin k → Fin q → Fin q → F)
    (z : F → Fin q → F)
    (hS : S ∈ affineZariskiClosure (commonLabelRestrictions F q k m L))
    (hcurve : ∀ c, ∃ P : F[X],
      (∀ t : F, t ≠ 0 → P.eval t =
        (u t c.h c.a * (∏ j, b t j (c.hOther j) (c.v j)) * z t c.g) * S c) ∧
      P.eval 0 = T c) :
    T ∈ affineZariskiClosure (commonLabelRestrictions F q k m L) := by
  choose P hP hP₀ using hcurve
  rw [← affineZariskiClosure_idem, ← funext hP₀]
  apply polynomialCurve_zero_mem_affineZariskiClosure
  intro t ht
  simp only [hP _ t ht]
  exact mapsTo_affineZariskiClosure_of_mul _
    (localScaling_preserves_commonLabelRestrictions q k m L (u t) (b t) (z t)) hS

/-- The two common labels of the target are independent. The first, present
at all old sites, also occurs at the new site. The second is common to the
`k + 1` sites of the intersection. -/
def commonLabelTarget (F : Type*) [Field F] {q k m : ℕ} (c : IncrementCoordinate q k m) : F :=
  if c.shared ∧ c.g = c.h ∧ ∀ j, c.v j = c.a then 1 else 0

/-- Starting with the two diagonals of dimensions `q` and
`2 (k + 1) (q - 1) + 1`, the product of the desired independent
`q`-diagonals belongs to the Zariski closure of their local restrictions. -/
theorem commonLabelTarget_mem_closure (F : Type*) [Field F] [Infinite F] (q k m : ℕ) :
    commonLabelTarget F ∈ affineZariskiClosure
      (commonLabelRestrictions F q k m (2 * (k + 1) * (q - 1) + 1)) := by
  classical
  let S (c : IncrementCoordinate q k m) : F :=
    if c.shared ∧ (c.g.val : ℤ) = c.h.val + (∑ j, ((c.v j).val : ℤ)) - (k : ℤ) * c.a.val
    then 1 else 0
  let T (c : IncrementCoordinate q k m) : F :=
    if c.shared ∧ (c.g.val : ℤ) = c.h.val ∧ (∑ j, ((c.v j).val : ℤ)) = (k : ℤ) * c.a.val
    then 1 else 0
  have hS : S ∈ affineZariskiClosure
      (commonLabelRestrictions F q k m (2 * (k + 1) * (q - 1) + 1)) :=
    subset_affineZariskiClosure _ (commonLabelEquation_mem_restrictions F q k m)
  have hT : T ∈ affineZariskiClosure
      (commonLabelRestrictions F q k m (2 * (k + 1) * (q - 1) + 1)) := by
    apply specialize_local_scalings
      (fun t h a ↦ t ^ (-(h.val : ℤ) ^ 2 + 2 * h.val * ((k : ℤ) * a.val)))
      (fun t _ h v ↦ t ^ (-(2 * (h.val : ℤ) * v.val)))
      (fun t g ↦ t ^ ((g.val : ℤ) ^ 2)) hS
    intro c
    by_cases hc : c.shared
    · obtain ⟨P, hP, hP₀⟩ := firstDiagonalSpecialization F
        (c.g.val : ℤ) c.h.val c.a.val (fun j ↦ ((c.v j).val : ℤ))
      refine ⟨P, fun t ht ↦ ?_, ?_⟩
      · rw [hP t ht]
        simp only [Fintype.card_fin, hc.1, S, hc, true_and]
        ac_rfl
      · simpa only [Fintype.card_fin, T, hc, true_and] using hP₀
    · exact ⟨0, by simp [S, hc], by simp [T, hc]⟩
  apply specialize_local_scalings
    (fun t _ a ↦ t ^ (-(k : ℤ) * (a.val : ℤ) ^ 2))
    (fun t _ _ v ↦ t ^ ((v.val : ℤ) ^ 2)) (fun _ _ ↦ 1) hT
  intro c
  by_cases hc : c.shared
  · obtain ⟨P, hP, hP₀⟩ := secondDiagonalSpecialization F
      (c.g.val : ℤ) c.h.val c.a.val (fun j ↦ ((c.v j).val : ℤ))
    refine ⟨P, fun t ht ↦ ?_, ?_⟩
    · rw [hP t ht]
      simp only [Fintype.card_fin, T, hc, true_and, one_mul, mul_comm]
    · simpa only [commonLabelTarget, hc, true_and, Nat.cast_inj, Fin.val_inj] using hP₀
  · exact ⟨0, by simp [T, hc], by simp [commonLabelTarget, hc]⟩

end

end SpectralBooks
end LinearAlgebra
end OAI
