import Mathlib.Data.Matrix.Block
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-! # A unit pivot from two shears over a semilocal ring

A matrix whose entries generate the unit ideal has a nonzero entry in every
residue field. In each field, adding a multiple of one row and then a multiple
of one column gives a nonzero bottom right entry. The Chinese remainder theorem
lifts the coefficients of these shears simultaneously.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R] {n : ℕ}

private theorem exists_affine_nonzero (x : Fin n ⊕ Unit → R) (hx : ∃ i, x i ≠ 0) :
    ∃ r : Fin n → R, x (.inr ()) + ∑ i, r i * x (.inl i) ≠ 0 := by
  classical
  by_cases h : x (.inr ()) = 0
  · obtain ⟨i | u, hi⟩ := hx
    · refine ⟨fun j => if i = j then 1 else 0, ?_⟩
      simpa [h, ite_mul] using hi
    · exact (hi (by cases u; exact h)).elim
  · exact ⟨fun _ => 0, by simpa using h⟩

private theorem exists_affine_bilinear_nonzero
    (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R) (hM : ∃ i j, M i j ≠ 0) :
    ∃ r c : Fin n → R,
      (M (.inr ()) (.inr ()) + ∑ i, r i * M (.inl i) (.inr ())) +
        ∑ j, c j * (M (.inr ()) (.inl j) + ∑ i, r i * M (.inl i) (.inl j)) ≠ 0 := by
  obtain ⟨i, j, hij⟩ := hM
  obtain ⟨r, hr⟩ := exists_affine_nonzero (fun k => M k j) ⟨i, hij⟩
  obtain ⟨c, hc⟩ := exists_affine_nonzero
    (fun l => M (.inr ()) l + ∑ k, r k * M (.inl k) l) ⟨j, hr⟩
  exact ⟨r, c, hc⟩

/-- Two shears on a primitive square matrix over a semilocal ring produce a unit
in its bottom right corner. The last row and last column have coefficient one. -/
theorem exists_semilocal_bilinear_unit_pivot [Finite (MaximalSpectrum R)]
    (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R)
    (hM : Ideal.span (Set.range (fun ij : (Fin n ⊕ Unit) × (Fin n ⊕ Unit) =>
      M ij.1 ij.2)) = ⊤) :
    ∃ r c : Fin n → R,
      IsUnit (((Matrix.fromBlocks 1 0 (fun (_ : Unit) i => r i) 1 :
        Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R) * M *
        (Matrix.fromBlocks 1 (fun i (_ : Unit) => c i) 0 1 :
          Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R)) (.inr ()) (.inr ())) := by
  classical
  let π (m : MaximalSpectrum R) := Ideal.Quotient.mk m.asIdeal
  have hex (m : MaximalSpectrum R) : ∃ i j, π m (M i j) ≠ 0 := by
    by_contra! h
    apply m.isMaximal.ne_top
    rw [eq_top_iff, ← hM, Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp (h i j)
  choose a b hab using fun m =>
    exists_affine_bilinear_nonzero (fun i j => π m (M i j)) (hex m)
  have lift (f : (m : MaximalSpectrum R) → R ⧸ m.asIdeal) :
      ∃ x : R, ∀ m, π m x = f m :=
    Ideal.pi_quotient_surjective
      (fun _ _ h => Ideal.isCoprime_of_isMaximal (fun e => h (MaximalSpectrum.ext e))) f
  choose r hr using fun i => lift (fun m => a m i)
  choose c hc using fun i => lift (fun m => b m i)
  refine ⟨r, c, ?_⟩
  by_contra hn
  obtain ⟨I, hI, hp⟩ := exists_max_ideal_of_mem_nonunits hn
  let m : MaximalSpectrum R := ⟨I, hI⟩
  have he := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  apply hab m
  change π m _ = 0 at he
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_unique, Matrix.fromBlocks,
    Matrix.of_apply, Sum.elim_inr, Sum.elim_inl, Matrix.one_apply_eq, one_mul, mul_one,
    map_add, map_sum, map_mul, hr, hc] at he
  simpa only [add_comm, mul_comm] using he

end FiniteFourier
end LinearAlgebra
end OAI
