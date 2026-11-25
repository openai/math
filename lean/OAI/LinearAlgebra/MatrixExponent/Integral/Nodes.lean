import OAI.LinearAlgebra.MatrixExponent.Integral.Model
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Integral nodes for arbitrarily long interpolation

Adjoin a root of X ∏ (X^j − 1) − 1. Its first powers are
units with pairwise unit differences.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Integral
open Finset Polynomial

abbrev O := ↥(integralClosure ℤ (AlgebraicClosure ℚ))

private theorem root (p : Polynomial ℤ) (hp : p.Monic) (hd : 0 < p.degree) :
    ∃ x : O, aeval x p = 1 := by
  let K := AlgebraicClosure ℚ
  have hdeg : (1 : Polynomial ℤ).degree < p.degree := by simpa using hd
  have hmon := hp.sub_of_left hdeg
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero K (p - 1)
    (by rw [degree_sub_eq_left_of_degree_lt hdeg]; exact hd.ne')
  let x : O := ⟨z, p - 1, hmon, hz⟩
  refine ⟨x, ?_⟩
  apply (FaithfulSMul.algebraMap_injective O K)
  rw [← aeval_algebraMap_apply, map_one]
  change aeval z p = 1
  simpa only [map_sub, map_one, sub_eq_zero] using hz

private theorem exceptional (n : ℕ) :
    ∃ x : O, IsUnit x ∧ ∀ j : ℕ, 0 < j → j ≤ n → IsUnit (x ^ j - 1) := by
  let P : Polynomial ℤ := X * ∏ j ∈ Icc 1 n, (X ^ j - 1)
  have hP : P.Monic := monic_X.mul (monic_prod_of_monic _ _ (by
    intro j hj
    exact (monic_X.pow j).sub_of_left (by
      rw [degree_one, degree_X_pow]
      exact_mod_cast (mem_Icc.mp hj).1)))
  have hdeg : 0 < P.degree := degree_pos_of_root hP.ne_zero (show P.IsRoot 0 by simp [P, IsRoot])
  obtain ⟨a, ha⟩ := root P hP hdeg
  simp only [P, map_mul, map_prod, map_sub, map_one, map_pow, aeval_X] at ha
  refine ⟨a, isUnit_of_dvd_one ⟨_, ha.symm⟩, fun j hj hj' => ?_⟩
  apply isUnit_of_dvd_one
  apply dvd_trans (dvd_prod_of_mem (fun i => a ^ i - 1) (mem_Icc.mpr ⟨hj, hj'⟩))
  exact ⟨a, by rw [mul_comm]; exact ha.symm⟩

theorem nodes (n : ℕ) : ∃ x : O, IsUnit x ∧
    IsUnit (Matrix.vandermonde (fun i : Fin n => x ^ i.val)).det := by
  obtain ⟨x, hx, he⟩ := exceptional n
  refine ⟨x, hx, ?_⟩
  rw [Matrix.det_vandermonde]
  apply IsUnit.prod_iff.mpr
  intro i _
  apply IsUnit.prod_iff.mpr
  intro j hj
  have hij : i < j := mem_Ioi.mp hj
  rw [show x ^ j.val - x ^ i.val = x ^ i.val * (x ^ (j.val - i.val) - 1) by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hij.le]]
  exact (hx.pow _).mul (he _ (by omega) (by omega))

end OAI.LinearAlgebra.MatrixExponent.Integral
end

section
/-! # Interpreting a ring circuit along a homomorphism into a field -/

namespace OAI.LinearAlgebra.MatrixExponent.Integral

variable {A F : Type*} [CommRing A] [Field F] {i j k m : ℕ} {a b c s : ℝ}

theorem Build.map {R : Type*} [CommRing R] {S T : Set A} {U : Set R} (h : Build S m T) (f : A →+* R)
    (hu : ∀ x ∈ S, f x ∈ U) : ∃ V, Build U m V ∧ ∀ x ∈ T, f x ∈ V := by
  induction h with
  | nil => exact ⟨U, .nil, hu⟩
  | add _ hx hy ih =>
    obtain ⟨V, h, hV⟩ := ih
    exact ⟨_, h.add (hV _ hx) (hV _ hy), by simpa only [Set.forall_mem_insert, map_add] using
      ⟨Set.mem_insert _ _, fun x hx => Set.mem_insert_of_mem _ (hV x hx)⟩⟩
  | sub _ hx hy ih =>
    obtain ⟨V, h, hV⟩ := ih
    exact ⟨_, h.sub (hV _ hx) (hV _ hy), by simpa only [Set.forall_mem_insert, map_sub] using
      ⟨Set.mem_insert _ _, fun x hx => Set.mem_insert_of_mem _ (hV x hx)⟩⟩
  | mul _ hx hy ih =>
    obtain ⟨V, h, hV⟩ := ih
    exact ⟨_, h.mul (hV _ hx) (hV _ hy), by simpa only [Set.forall_mem_insert, map_mul] using
      ⟨Set.mem_insert _ _, fun x hx => Set.mem_insert_of_mem _ (hV x hx)⟩⟩

theorem Build.embed {S T : Set F} (h : Build S m T) : MatrixExponent.Build S m T := by
  induction h with
  | nil => exact .nil
  | add _ hx hy ih => exact ih.add hx hy
  | sub _ hx hy ih => exact ih.sub hx hy
  | mul _ hx hy ih => exact ih.mul hx hy

theorem Computes.field (h : Computes A i j k m) (f : A →+* F) : Rectangle.Computes F i j k m := by
  let g := MvPolynomial.eval₂Hom ((algebraMap F (Rectangle.Rat F i j k)).comp f) (Rectangle.input F)
  have he (u : Var i j k) : g (input A u) = Rectangle.input F u := by simp [g, input]
  obtain ⟨T, hT, ho⟩ := h
  obtain ⟨V, hV, hf⟩ := hT.map (U := Rectangle.initial F i j k) g (by
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · left
      exact ⟨f x, by simp [g]⟩
    · right
      exact ⟨x, (he _).symm⟩)
  refine ⟨V, hV.embed, fun p => ?_⟩
  simpa only [output, Rectangle.output, map_sum, map_mul, he] using hf _ (ho p)

theorem Admissible.field (h : Admissible A a b c s) (f : A →+* F) : Rectangle.Admissible F a b c s := by
  intro ε hε
  obtain ⟨C, hC, hf⟩ := h ε hε
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨m, hm, hcost⟩ := hf n hn
  exact ⟨m, hm.field f, hcost⟩

end OAI.LinearAlgebra.MatrixExponent.Integral
end
