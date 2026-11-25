import OAI.LinearAlgebra.FiniteFourier.SynchronizedKernel
import OAI.LinearAlgebra.FiniteFourier.PrimeFourierSectors.FourierSectorPadding
import OAI.LinearAlgebra.FiniteFourier.PrimeFourierSectors.FourierSectorGenerators
import OAI.LinearAlgebra.FiniteFourier.TernaryShearIsolation

/-! # Local Fourier words on selected registers

A local word can act on chosen registers of any larger array while preserving the
contents of its other registers. Neither relabeling nor adjoining identity wires
increases its synchronized slot count.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
  [DecidableEq J] {p n : ℕ} {ζ s : R}

omit [Fintype I] [Fintype J] in
private theorem reindex_kernelMonomial (e : I ≃ J) (q : Equiv.Perm I) (c : I → R) :
    (kernelMonomial q c).submatrix e.symm e.symm =
      kernelMonomial ((e.symm.trans q).trans e) (c ∘ e.symm) := by
  ext i j
  simp [kernelMonomial, submatrix, e.eq_symm_apply]
  split <;> simp_all

/-- Transport every synchronized word slot through the same coordinate bijection. -/
theorem KernelWord.relabel {A : Matrix I I R} (hA : KernelWord p ζ n A) (e : I ≃ J) :
    KernelWord p ζ n (A.submatrix e.symm e.symm) := by
  induction n generalizing A with
  | zero =>
    obtain rfl : A = 1 := hA
    exact Matrix.submatrix_one_equiv e.symm
  | succ n ih =>
    obtain ⟨q, c, F, P, hF, hP, rfl⟩ := hA
    refine ⟨(e.symm.trans q).trans e, c ∘ e.symm, F.submatrix e.symm e.symm, _, ?_, ih hP, ?_⟩
    · rcases hF with rfl | h
      · exact Or.inl (Matrix.submatrix_one_equiv e.symm)
      · exact Or.inr ⟨h.some.reindex e⟩
    · rw [← reindex_kernelMonomial]
      simp only [Matrix.submatrix_mul_equiv]

omit [Fintype I] [Fintype J] in
private theorem addIdentity_kernelMonomial (q : Equiv.Perm I) (c : I → R) :
    fromBlocks (kernelMonomial q c) 0 0 (1 : Matrix J J R) =
      kernelMonomial (q.sumCongr (Equiv.refl J)) (Sum.elim c fun _ => 1) := by
  ext (i | i) (j | j) <;> simp [fromBlocks, kernelMonomial, Matrix.one_apply]

/-- Adjoin any number of occupied identity wires without using an additional slot. -/
theorem KernelWord.addIdentity {A : Matrix I I R} (hA : KernelWord p ζ n A) (J : Type)
    [Fintype J] [DecidableEq J] :
    KernelWord p ζ n (fromBlocks A 0 0 (1 : Matrix J J R)) := by
  induction n generalizing A with
  | zero =>
    obtain rfl : A = 1 := hA
    exact fromBlocks_one
  | succ n ih =>
    obtain ⟨q, c, F, P, hF, hP, rfl⟩ := hA
    refine ⟨q.sumCongr (Equiv.refl J), Sum.elim c (fun _ => 1), fromBlocks F 0 0 1,
      _, ?_, ih hP, ?_⟩
    · rcases hF with rfl | h
      · exact Or.inl fromBlocks_one
      · exact Or.inr ⟨h.some.addIdentity J⟩
    · rw [← addIdentity_kernelMonomial]
      simp [fromBlocks_multiply]

private theorem exists_equiv_inl_pair {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (hc : Fintype.card I ≤ Fintype.card J) {a b : I} {u v : J} (hab : a ≠ b) (huv : u ≠ v) :
    ∃ e : I ⊕ Fin (Fintype.card J - Fintype.card I) ≃ J,
      e (.inl a) = u ∧ e (.inl b) = v := by
  let e : I ⊕ Fin (Fintype.card J - Fintype.card I) ≃ J :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  let f := e.trans (Equiv.swap (e (.inl a)) u)
  have hfa : f (.inl a) = u := by simp [f]
  have hne : u ≠ f (.inl b) := by
    rw [← hfa]
    exact f.injective.ne (fun h => hab (Sum.inl.inj h))
  exact ⟨f.trans (Equiv.swap (f (.inl b)) v),
    by simpa [hfa] using Equiv.swap_apply_of_ne_of_ne hne huv, by simp⟩

/-- A word that adds register `b` into `a` with coefficient `s` can implement
the same transvection on any ordered pair of distinct registers in a larger array. -/
theorem KernelWord.transvection_of_card_le {a b : I}
    (h : KernelWord p ζ n (transvection a b s)) (hab : a ≠ b)
    {u v : J} (huv : u ≠ v) (hc : Fintype.card I ≤ Fintype.card J) :
    KernelWord p ζ n (transvection u v s) := by
  let D := Fin (Fintype.card J - Fintype.card I)
  obtain ⟨e, heu, hev⟩ := exists_equiv_inl_pair hc hab huv
  have hpad : fromBlocks (transvection a b s) 0 0 (1 : Matrix D D R) =
      transvection (Sum.inl a) (Sum.inl b) s := by
    ext (i | i) (j | j) <;> simp [fromBlocks, transvection, Matrix.one_apply, Matrix.single_apply]
  have hw := (h.addIdentity D).relabel e
  rw [hpad] at hw
  simpa [transvection, Matrix.submatrix_add, Matrix.submatrix_one_equiv, heu, hev] using hw

/-- A ternary word embeds slot for slot in the common synchronized word format. -/
theorem RingTernaryWord.kernelWord {A : Matrix (Fin 3) (Fin 3) R}
    (h : RingTernaryWord ζ n A) : KernelWord 3 ζ n A := by
  induction h with
  | id => exact KernelWord.identity 3 ζ (Fin 3)
  | monomial q c => exact KernelWord.monomial 3 ζ q (fun i => c i)
  | fourier => exact KernelWord.fourier (PrimeFourierSectors.full 3 ζ)
  | mul _ _ ih₁ ih₂ => exact ih₁.mul ih₂

/-- Place the protected ternary shear on a prescribed ordered pair. The
unselected registers, including the third register of the Fourier block, retain
their initial values. -/
theorem kernelWord_ternary_semilocalShear [Finite (MaximalSpectrum R)] (ζ a : R)
    (hζ : ζ^2 + ζ + 1 = 0) (h3 : IsUnit (3 : R)) (ha9 : a^9 = 1)
    (hres : ∀ m : MaximalSpectrum R, IsPrimitiveRoot (Ideal.Quotient.mk m.asIdeal a) 9)
    {u v : I} (huv : u ≠ v) (hc : 3 ≤ Fintype.card I) (s : R) :
    KernelWord 3 ζ 56 (transvection u v s) :=
  (ringTernaryWord_semilocalShear ζ a hζ h3 ha9 hres s).kernelWord.transvection_of_card_le
    (by decide) huv (by simpa using hc)

end FiniteFourier
end LinearAlgebra
end OAI
