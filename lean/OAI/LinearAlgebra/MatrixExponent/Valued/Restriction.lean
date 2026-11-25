import OAI.LinearAlgebra.MatrixExponent.Spectral.Semiring
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Restrictions with entries in a subring

The tensors themselves still have coefficients in the ambient field.
For a valuation ring this relation allows only integral substitutions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral

variable {K S : Type} [Field K] [Fintype S] (O : Subring K)
variable {A B C D : Raw K S}

def Restricts (A B : Raw K S) : Prop :=
  ∃ L : (s : S) → B.leg s → A.leg s → K, (∀ s x y, L s x y ∈ O) ∧
    ∀ x, B.coeff x = ∑ i : A.term, ∏ s, ∑ y : A.leg s, L s (x s) y * A.factor i s y

variable {O}

theorem top_restricts (h : A.Restricts B) : Restricts ⊤ A B := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, fun _ _ _ => trivial, hL⟩

theorem restricts_iff [DecidableEq S] (A B : Raw K S) :
    Restricts O A B ↔
      ∃ L : (s : S) → B.leg s → A.leg s → K, (∀ s x y, L s x y ∈ O) ∧
        ∀ x, B.coeff x = ∑ y : ∀ s, A.leg s, (∏ s, L s (x s) (y s)) * A.coeff y := by
  simp only [Restricts, Raw.expand]

theorem Restricts.forget (h : Restricts O A B) : A.Restricts B := by
  obtain ⟨L, _, hh⟩ := h
  exact ⟨L, hh⟩

theorem Restricts.pullback (f : ∀ s, B.leg s → A.leg s)
    (h : ∀ x, B.coeff x = A.coeff (fun s => f s (x s))) : Restricts O A B := by
  classical
  refine ⟨fun s x y => if y = f s x then 1 else 0, ?_, fun x => ?_⟩
  · intro s x y
    by_cases h : y = f s x <;> simp [h]
  · rw [h]
    simp [Raw.coeff, ite_mul]

theorem Restricts.refl (A : Raw K S) : Restricts O A A :=
  Restricts.pullback (fun _ x => x) (fun _ => rfl)

theorem Restricts.trans (h : Restricts O A B) (g : Restricts O B C) : Restricts O A C := by
  classical
  obtain ⟨L, hl, h⟩ := h
  obtain ⟨M, hm, g⟩ := g
  refine ⟨fun s x z => ∑ y, M s x y * L s y z,
    fun s x z => O.sum_mem (fun y _ => O.mul_mem (hm s x y) (hl s y z)), fun x => ?_⟩
  rw [g, B.expand]
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun s y => M s (x s) y * ∑ z, L s y z * A.factor i s z)]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

def equiv (O : Subring K) : Setoid (Raw K S) where
  r A B := Restricts O A B ∧ Restricts O B A
  iseqv := ⟨fun A => ⟨.refl A, .refl A⟩, fun h => ⟨h.2, h.1⟩,
    fun h g => ⟨h.1.trans g.1, g.2.trans h.2⟩⟩

theorem forget_equiv (h : (equiv O).r A B) : A ≈ B := ⟨h.1.forget, h.2.forget⟩

theorem equiv_coeff (f : ∀ s, A.leg s ≃ B.leg s)
    (h : ∀ x, A.coeff x = B.coeff (fun s => f s (x s))) : (equiv O).r A B := by
  refine ⟨Restricts.pullback (fun s => (f s).symm) ?_, Restricts.pullback (fun s => f s) h⟩
  intro x
  simp only [h, Equiv.apply_symm_apply]

theorem relabel (e : A.term ≃ B.term) (f : ∀ s, A.leg s ≃ B.leg s)
    (h : ∀ i s x, A.factor i s x = B.factor (e i) s (f s x)) : (equiv O).r A B := by
  refine equiv_coeff f fun x => ?_
  simp only [Raw.coeff, h]
  exact e.sum_comp (fun i => ∏ s, B.factor i s (f s (x s)))

theorem Restricts.mul (h : Restricts O A B) (g : Restricts O C D) :
    Restricts O (A * C) (B * D) := by
  obtain ⟨L, hl, hL⟩ := h
  obtain ⟨M, hm, hM⟩ := g
  refine ⟨fun s x y => L s x.1 y.1 * M s x.2 y.2,
    fun s x y => O.mul_mem (hl _ _ _) (hm _ _ _), fun x => ?_⟩
  rw [Raw.coeff_mul, hL, hM]
  change _ = ∑ i : A.term × C.term, ∏ s, ∑ y : A.leg s × C.leg s,
    L s (x s).1 y.1 * M s (x s).2 y.2 * (A.factor i.1 s y.1 * C.factor i.2 s y.2)
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_mul_mul_comm _ _ _ _

theorem Restricts.add (h : Restricts O A B) (g : Restricts O C D) :
    Restricts O (A + C) (B + D) := by
  obtain ⟨L, hl, hL⟩ := h
  obtain ⟨M, hm, hM⟩ := g
  let N (s : S) : B.leg s ⊕ D.leg s → A.leg s ⊕ C.leg s → K :=
    Sum.elim (fun b => Sum.elim (L s b) (fun _ => 0))
      (fun d => Sum.elim (fun _ => 0) (M s d))
  have left (i : A.term) (s : S) (y : A.leg s ⊕ C.leg s) :
      (A + C).factor (.inl i) s y = Sum.elim (A.factor i s) (fun _ => 0) y := rfl
  have right (i : C.term) (s : S) (y : A.leg s ⊕ C.leg s) :
      (A + C).factor (.inr i) s y = Sum.elim (fun _ => 0) (C.factor i s) y := rfl
  refine ⟨N, ?_, fun x => ?_⟩
  · rintro s (x | x) (y | y) <;> simp [N, hl, hm]
  change (∑ i : B.term ⊕ D.term, ∏ s, (B + D).factor i s (x s)) =
    ∑ i : A.term ⊕ C.term, ∏ s, ∑ y : A.leg s ⊕ C.leg s,
      N s (x s) y * (A + C).factor i s y
  simp only [Fintype.sum_sum_type, left, right]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Raw.extend B.factor (fun i s z => ∑ y, L s z y * A.factor i s y) hL ?_
    intro s
    cases x s with
    | inl z => exact Or.inl ⟨z, fun _ => rfl, fun _ => by simp [N]⟩
    | inr z => exact Or.inr ⟨fun _ => rfl, fun _ => by simp [N]⟩
  · refine Raw.extend D.factor (fun i s z => ∑ y, M s z y * C.factor i s y) hM ?_
    intro s
    cases x s with
    | inl z => exact Or.inr ⟨fun _ => rfl, fun _ => by simp [N]⟩
    | inr z => exact Or.inl ⟨z, fun _ => rfl, fun _ => by simp [N]⟩

end OAI.LinearAlgebra.MatrixExponent.Valued
