import OAI.LinearAlgebra.FiniteFourier.BatchedValuation

/-! # Lifting an affine specialization with one projective coordinate -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks MvPolynomial
open scoped Classical

variable {K L S : Type*} [Field K] [Field L] {ι κ : Type} [Fintype κ] [Nonempty κ]

omit [Nonempty κ] in
private theorem generic_nonzero_coordinate (f : (S → K) →+* L) (y : S → κ → K)
    (hy : ∀ s, ∃ i, y s i ≠ 0) : ∃ i, f (fun s => y s i) ≠ 0 := by
  let u (i : κ) : S → K := fun s => y s i
  have hz : ∏ i, (1 - u i * (u i)⁻¹) = 0 := by
    funext s
    rw [Finset.prod_apply]
    obtain ⟨i, hi⟩ := hy s
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [u, hi])
  by_contra! h
  have he := congrArg f hz
  have hu : ∀ i, f (u i) = 0 := h
  simp [map_prod, hu] at he

private theorem generic_normalized_coordinates (f : (S → K) →+* L)
    (V : ValuationSubring L) (y : S → κ → K) (hy : ∀ s, ∃ i, y s i ≠ 0) :
    ∃ i, f (fun s => y s i) ≠ 0 ∧ ∀ j, f (fun s => y s j / y s i) ∈ V := by
  let u (i : κ) : S → K := fun s => y s i
  obtain ⟨i, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => V.valuation (f (u i))) Finset.univ_nonempty
  have hi : f (u i) ≠ 0 := by
    obtain ⟨j, hj⟩ := generic_nonzero_coordinate f y hy
    intro he
    have hj' := hmax j (Finset.mem_univ j)
    rw [he, map_zero, nonpos_iff_eq_zero, map_eq_zero] at hj'
    exact hj hj'
  refine ⟨i, hi, fun j => ?_⟩
  obtain ⟨t, ht⟩ := (V.valuation_le_iff _ _).mp (hmax j (Finset.mem_univ j))
  have he : (u j / u i) * u i * u i = u j * u i := by
    funext s
    simp only [Pi.mul_apply, Pi.div_apply]
    by_cases hs : u i s = 0
    · simp [hs]
    · rw [div_mul_cancel₀ _ hs]
  have h := congrArg f he
  simp only [map_mul] at h
  have heq := mul_right_cancel₀ hi ((mul_right_cancel₀ hi h).trans ht.symm)
  exact show f (u j / u i) ∈ V from heq.symm ▸ t.property

theorem projective_chart_specialization [Finite ι] [IsAlgClosed K]
    (x : S → ι → K) (y : S → κ → K) (hy : ∀ s, ∃ i, y s i ≠ 0)
    (x₀ : ι → K) (hx : x₀ ∈ affineZariskiClosure (Set.range x)) :
    ∃ (i : κ) (z : κ → K), z i = 1 ∧
      Sum.elim x₀ z ∈ affineZariskiClosure
        ((fun s => Sum.elim (x s) (fun j => y s j / y s i)) '' {s | y s i ≠ 0}) := by
  obtain ⟨L, fieldL, f, V, hb, hm⟩ := exists_valuation_specialization x x₀ hx
  obtain ⟨i, hi, hn⟩ := generic_normalized_coordinates f V y hy
  let w (s : S) := Sum.elim (x s) (fun j => y s j / y s i)
  have hc (c : K) : f (fun _ => c) ∈ V := by
    simpa only [show familyEval x (C c) = fun _ => c from funext fun s => by
      simp [familyEval_apply]] using hb (C c)
  have hw (k : ι ⊕ κ) : f (fun s => w s k) ∈ V := by
    cases k with
    | inl j =>
      have he : familyEval x (X j) = fun s => x s j := funext fun s => by simp [familyEval_apply]
      exact he ▸ hb (X j)
    | inr j => exact hn j
  obtain ⟨t, ht⟩ := exists_residue_tuple f V w hc hw
  have hx' (j : ι) : t (.inl j) = x₀ j := by
    have he : familyEval w (X (.inl j) - C (x₀ j)) = familyEval x (X j - C (x₀ j)) := by
      funext s
      simp [familyEval_apply, w]
    have hp := ht (X (.inl j) - C (x₀ j)) (by rw [he]; exact hm _ (by simp))
    simpa [sub_eq_zero] using hp
  have hcl : t ∈ affineZariskiClosure (w '' {s | y s i ≠ 0}) := by
    intro p hp
    have he : familyEval w p * (fun s => y s i) = 0 := by
      funext s
      rw [Pi.mul_apply, familyEval_apply]
      by_cases hs : y s i = 0
      · simp [hs]
      · rw [hp _ ⟨s, hs, rfl⟩, zero_mul]; rfl
    apply ht
    have hzero : f (familyEval w p) = 0 := (mul_eq_zero.mp (by
      rw [← map_mul, he, map_zero])).resolve_right hi
    rw [hzero]
    exact V.nonunits.zero_mem
  have hti := hcl (X (.inr i) - 1) (by
    rintro _ ⟨s, hs, rfl⟩
    simp [w, div_self (show y s i ≠ 0 from hs)])
  refine ⟨i, fun j => t (.inr j), by simpa [sub_eq_zero] using hti, ?_⟩
  have he : Sum.elim x₀ (fun j => t (.inr j)) = t := by
    funext k
    cases k with
    | inl j => exact (hx' j).symm
    | inr j => rfl
  rw [he]
  exact hcl

end FiniteFourier
end LinearAlgebra
end OAI
