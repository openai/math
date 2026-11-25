import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Finite.Basic

/-! # Equations for the values of a rational function on a finite fiber

To bound poles in §10.2, the elimination pencil for a rational function must discard
all points where the denominator vanishes. The first extra coordinate is its inverse.
The coefficient variable `W` records the value of the function, leaving the parameter
`t` in the ground ring `Polynomial K`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {K E I : Type*} [Field K] [Field E] {h : ℕ}

/-- Insert the inverse coordinate at position zero and view coefficients as constant in W. -/
noncomputable def ratioLift (p : MvPolynomial (Fin h) (Polynomial K)) :
    MvPolynomial (Fin (h+1)) (Polynomial (Polynomial K)) :=
  map Polynomial.C (rename Fin.succ p)

/-- Equations for the graph of `A/B` on the part of the fiber where `B` is nonzero. -/
noncomputable def ratioSystem (g : I → MvPolynomial (Fin h) (Polynomial K))
    (A B : MvPolynomial (Fin h) (Polynomial K)) :
    I ⊕ Bool → MvPolynomial (Fin (h+1)) (Polynomial (Polynomial K))
  | .inl i => ratioLift (g i)
  | .inr false => X 0 * ratioLift B - 1
  | .inr true => C Polynomial.X * ratioLift B - ratioLift A

private theorem eval_ratioLift (φ : Polynomial K →+* E) (w : E) (y : Fin (h+1) → E)
    (p : MvPolynomial (Fin h) (Polynomial K)) :
    eval₂ (Polynomial.eval₂RingHom φ w) y (ratioLift p) = eval₂ φ (y ∘ Fin.succ) p := by
  rw [ratioLift, eval₂_map, Polynomial.eval₂RingHom_comp_C, eval₂_rename]

/-- The graph equations admit exactly the ratios at points where the denominator is nonzero. -/
theorem ratioSystem_solution_iff (φ : Polynomial K →+* E) (w : E)
    (g : I → MvPolynomial (Fin h) (Polynomial K)) (A B : MvPolynomial (Fin h) (Polynomial K)) :
    (∃ y : Fin (h+1) → E, ∀ i, eval₂ (Polynomial.eval₂RingHom φ w) y (ratioSystem g A B i) = 0) ↔
      ∃ x : Fin h → E, (∀ i, eval₂ φ x (g i) = 0) ∧ eval₂ φ x B ≠ 0 ∧
        w = eval₂ φ x A / eval₂ φ x B := by
  constructor
  · rintro ⟨y, hy⟩
    let x := y ∘ Fin.succ
    have hi : y 0 * eval₂ φ x B = 1 := by
      simpa [x, ratioSystem, eval₂_sub, eval₂_mul, eval_ratioLift, sub_eq_zero] using hy (.inr false)
    have hb : eval₂ φ x B ≠ 0 := fun hz => by simp [hz] at hi
    refine ⟨x, fun i => ?_, hb, (eq_div_iff hb).2 ?_⟩
    · simpa [x, ratioSystem, eval_ratioLift] using hy (.inl i)
    · simpa [x, ratioSystem, eval₂_sub, eval₂_mul, eval_ratioLift, sub_eq_zero] using hy (.inr true)
  · rintro ⟨x, hg, hb, rfl⟩
    let y := Fin.cons (α := fun _ => E) (eval₂ φ x B)⁻¹ x
    have hxy : y ∘ Fin.succ = x := by ext i; simp [y]
    refine ⟨y, fun i => ?_⟩
    rcases i with i | ( _ | _ )
    · simpa [ratioSystem, eval_ratioLift, hxy] using hg i
    · simp [ratioSystem, eval₂_sub, eval₂_mul, eval_ratioLift, hxy, y, hb]
    · simp [ratioSystem, eval₂_sub, eval₂_mul, eval_ratioLift, hxy, hb]

/-- Only finiteness of the locus where the denominator is nonzero is needed to
control the value image. -/
theorem finite_ratioSystem_parameters_of_domain (φ : Polynomial K →+* E)
    (g : I → MvPolynomial (Fin h) (Polynomial K)) (A B : MvPolynomial (Fin h) (Polynomial K))
    (hfin : {x : Fin h → E | (∀ i, eval₂ φ x (g i) = 0) ∧ eval₂ φ x B ≠ 0}.Finite) :
    {w : E | ∃ y : Fin (h+1) → E, ∀ i,
      eval₂ (Polynomial.eval₂RingHom φ w) y (ratioSystem g A B i) = 0}.Finite := by
  apply (hfin.image (fun x => eval₂ φ x A / eval₂ φ x B)).subset
  intro w hw
  obtain ⟨x, hx, hB, rfl⟩ := (ratioSystem_solution_iff φ w g A B).mp hw
  exact ⟨x, ⟨hx, hB⟩, rfl⟩

/-- A finite geometric fiber gives finitely many values of the ratio. The denominator
need only be nonzero at the selected point. -/
theorem finite_ratioSystem_parameters (φ : Polynomial K →+* E)
    (g : I → MvPolynomial (Fin h) (Polynomial K)) (A B : MvPolynomial (Fin h) (Polynomial K))
    (hfin : {x : Fin h → E | ∀ i, eval₂ φ x (g i) = 0}.Finite) :
    {w : E | ∃ y : Fin (h+1) → E, ∀ i,
      eval₂ (Polynomial.eval₂RingHom φ w) y (ratioSystem g A B i) = 0}.Finite := by
  exact finite_ratioSystem_parameters_of_domain φ g A B (hfin.subset fun _ h => h.1)

private theorem degree_ratioLift (p : MvPolynomial (Fin h) (Polynomial K)) :
    (ratioLift p).totalDegree ≤ p.totalDegree := by
  refine le_trans ?_ (totalDegree_rename_le Fin.succ p)
  apply Finset.sup_le
  intro m hm
  apply le_totalDegree
  exact support_map_subset Polynomial.C _ hm

/-- Total degree in the fiber coordinates and the inverse coordinate. -/
theorem ratioSystem_totalDegree_le {d : ℕ} (g : I → MvPolynomial (Fin h) (Polynomial K))
    (A B : MvPolynomial (Fin h) (Polynomial K)) (hg : ∀ i, (g i).totalDegree ≤ d)
    (hA : A.totalDegree ≤ d) (hB : B.totalDegree ≤ d) (i : I ⊕ Bool) :
    (ratioSystem g A B i).totalDegree ≤ d+1 := by
  rcases i with i | ( _ | _ )
  · exact (degree_ratioLift _).trans ((hg i).trans (Nat.le_succ d))
  · apply (totalDegree_sub ..).trans (max_le ?_ ?_)
    · apply (totalDegree_mul ..).trans
      rw [totalDegree_X, Nat.add_comm]
      exact Nat.add_le_add_right ((degree_ratioLift _).trans hB) _
    · simp
  · apply (totalDegree_sub ..).trans (max_le ?_ ?_)
    · apply (totalDegree_mul ..).trans
      rw [totalDegree_C, zero_add]
      exact (degree_ratioLift _).trans (hB.trans (Nat.le_succ d))
    · exact (degree_ratioLift _).trans (hA.trans (Nat.le_succ d))

private theorem coeff_ratioLift (p : MvPolynomial (Fin h) (Polynomial K))
    (m : Fin (h+1) →₀ ℕ) :
    (ratioLift p).coeff m = Polynomial.C ((rename Fin.succ p).coeff m) := by
  rw [ratioLift, coeff_map]

private theorem tdegree_renamed {e : ℕ} (p : MvPolynomial (Fin h) (Polynomial K))
    (hp : ∀ m, (p.coeff m).natDegree ≤ e) (m : Fin (h+1) →₀ ℕ) :
    ((rename Fin.succ p).coeff m).natDegree ≤ e := by
  by_cases hz : (rename Fin.succ p).coeff m = 0
  · simp [hz]
  obtain ⟨u, rfl, _⟩ := coeff_rename_ne_zero Fin.succ p m hz
  rw [coeff_rename_mapDomain _ (Fin.succ_injective h)]
  exact hp u

/-- Every coefficient of the graph equations is at most linear in the value parameter W. -/
theorem ratioSystem_Wdegree_le (g : I → MvPolynomial (Fin h) (Polynomial K))
    (A B : MvPolynomial (Fin h) (Polynomial K)) (i : I ⊕ Bool) (m : Fin (h+1) →₀ ℕ) :
    ((ratioSystem g A B i).coeff m).natDegree ≤ 1 := by
  classical
  rcases i with i | ( _ | _ )
  · simp [ratioSystem, coeff_ratioLift]
  · rw [ratioSystem, coeff_sub, coeff_X_mul', coeff_one]
    apply (Polynomial.natDegree_sub_le ..).trans (max_le ?_ ?_)
    · split <;> simp [coeff_ratioLift]
    · split <;> simp
  · rw [ratioSystem, coeff_sub, coeff_C_mul, coeff_ratioLift, coeff_ratioLift]
    apply (Polynomial.natDegree_sub_le ..).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_mul_le ..).trans (by simp)
    · simp

/-- Every t-coefficient retains the original t-degree bound, also after introducing W. -/
theorem ratioSystem_tdegree_le {e : ℕ} (g : I → MvPolynomial (Fin h) (Polynomial K))
    (A B : MvPolynomial (Fin h) (Polynomial K)) (hg : ∀ i m, ((g i).coeff m).natDegree ≤ e)
    (hA : ∀ m, (A.coeff m).natDegree ≤ e) (hB : ∀ m, (B.coeff m).natDegree ≤ e)
    (i : I ⊕ Bool) (m : Fin (h+1) →₀ ℕ) (j : ℕ) :
    (((ratioSystem g A B i).coeff m).coeff j).natDegree ≤ e := by
  classical
  rcases i with i | ( _ | _ )
  · rw [ratioSystem, coeff_ratioLift, Polynomial.coeff_C]
    split
    · exact tdegree_renamed _ (hg i) _
    · simp
  · rw [ratioSystem, coeff_sub, Polynomial.coeff_sub, coeff_X_mul', coeff_one]
    apply (Polynomial.natDegree_sub_le ..).trans (max_le ?_ ?_)
    · split
      · rw [coeff_ratioLift, Polynomial.coeff_C]
        split
        · exact tdegree_renamed _ hB _
        · simp
      · simp
    · split
      · rw [Polynomial.coeff_one]
        split <;> simp
      · simp
  · rw [ratioSystem, coeff_sub, Polynomial.coeff_sub, coeff_C_mul, coeff_ratioLift, coeff_ratioLift,
      mul_comm Polynomial.X, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    apply (Polynomial.natDegree_sub_le ..).trans (max_le ?_ ?_)
    · split
      · exact tdegree_renamed _ hB _
      · simp
    · split
      · exact tdegree_renamed _ hA _
      · simp

end Branch

end BorderVNP
end Computability
end OAI
