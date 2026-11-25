import OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice
import OAI.LinearAlgebra.SpectralBooks.TriangleAPFormat
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct

/-! # The diagonal inside the arithmetic-progression tensor

The triples `(2s, s+t, 2t)` for `s,t < r` are arithmetic progressions in
`Fin (2*r)`. At each of the three sites the incident pair determines both
parameters. Selecting those local pairs therefore leaves an independent
common label of size `r²`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open SiteTensor

private def twiceLabel {r : ℕ} (s : Fin r) : Fin (2*r) := ⟨2*s.val, by omega⟩
private def sumLabel {r : ℕ} (s t : Fin r) : Fin (2*r) := ⟨s.val+t.val, by omega⟩

private def progression {r : ℕ} (a : Fin r × Fin r) : Fin (2*r) × Fin (2*r) × Fin (2*r) :=
  (twiceLabel a.1, sumLabel a.1 a.2, twiceLabel a.2)

private def readPair {r : ℕ} (i : Fin 3) (a : Fin r × Fin r) :=
  triangleWireTerm (2*r) (progression a) i

private theorem progression_weight {r : ℕ} (a : Fin r × Fin r) :
    let s := progression a
    (s.1.val : ℤ) - 2 * (s.2.1.val : ℤ) + (s.2.2.val : ℤ) = 0 := by
  simp [progression, twiceLabel, sumLabel]
  ring

private theorem coherent_of_progression {r : ℕ} (x : Fin 3 → Fin r × Fin r)
    (s : Fin (2*r) × Fin (2*r) × Fin (2*r))
    (hread : (fun i ↦ readPair i (x i)) = triangleWireTerm (2*r) s)
    (hAP : (s.1.val : ℤ) - 2 * s.2.1.val + s.2.2.val = 0) : ∀ i, x i = x 0 := by
  have h₀ : (twiceLabel (x 0).1, sumLabel (x 0).1 (x 0).2) = (s.1, s.2.1) := congrFun hread 0
  have h₁ : (sumLabel (x 1).1 (x 1).2, twiceLabel (x 1).2) = (s.2.1, s.2.2) := congrFun hread 1
  have h₂ : (twiceLabel (x 2).2, twiceLabel (x 2).1) = (s.2.2, s.1) := congrFun hread 2
  have first {a b c d : Fin (2*r)} (h : (a,b) = (c,d)) : a.val = c.val := congrArg (fun p ↦ p.1.val) h
  have second {a b c d : Fin (2*r)} (h : (a,b) = (c,d)) : b.val = d.val := congrArg (fun p ↦ p.2.val) h
  have h0a := first h₀
  have h0b := second h₀
  have h1a := first h₁
  have h1b := second h₁
  have h2a := first h₂
  have h2b := second h₂
  simp only [twiceLabel, sumLabel] at h0a h0b h1a h1b h2a h2b
  intro i
  fin_cases i
  · rfl
  · change x 1 = x 0
    apply Prod.ext <;> apply Fin.ext <;> omega
  · change x 2 = x 0
    apply Prod.ext <;> apply Fin.ext <;> omega

private theorem triangleAPTensor_eq_indicator (K : Type*) [Field K] (q : ℕ)
    (x : Fin 3 → Fin q × Fin q) :
    triangleAPTensor K q x = if ∃ s : Fin q × Fin q × Fin q, x = triangleWireTerm q s ∧
      (s.1.val : ℤ) - 2 * s.2.1.val + s.2.2.val = 0 then 1 else 0 := by
  classical
  unfold triangleAPTensor
  split_ifs with h
  · obtain ⟨s, hs, hp⟩ := h
    rw [Finset.sum_eq_single s]
    · simp [hs,hp]
    · intro t _ hts
      exact ite_eq_right fun hc ↦ hts (triangleWireTerm_injective q (hc.1.symm.trans hs))
    · simp
  · apply Finset.sum_eq_zero
    intro s _
    exact ite_eq_right fun hp ↦ h ⟨s,hp⟩

/-- Projecting to the incident pairs of the indicated progressions supplies
one common independent pair `(s,t)` at the three sites. -/
theorem diagonal_restricts_triangleAPTensor (K : Type*) [Field K] (r : ℕ) :
    Crossing.IsRestriction (Raw.diagonal (Fin 3) K (Fin r × Fin r)).coeff (triangleAPTensor K (2*r)) := by
  classical
  let Y : Raw.{0} (Fin 3) K := ⟨fun _ ↦ Fin (2*r) × Fin (2*r), fun _ ↦ inferInstance, triangleAPTensor K (2*r)⟩
  apply Raw.restrict_by_read (X := Raw.diagonal (Fin 3) K (Fin r × Fin r)) (Y := Y) readPair
  intro x
  change (Raw.diagonal (Fin 3) K (Fin r × Fin r)).coeff x = triangleAPTensor K _ (fun i ↦ readPair i (x i))
  rw [Raw.diagonal_coeff_at (0 : Fin 3) x, triangleAPTensor_eq_indicator]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨progression (x 0), funext (fun i ↦ congrArg (readPair i) (h i)), progression_weight _⟩
  · rintro ⟨s, hs, hp⟩
    exact coherent_of_progression x s hs hp

end SpectralBooks
end LinearAlgebra
end OAI
