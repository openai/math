import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.BigOperators

/-! # The first vanishing generator substitution

Section 14 specializes the seed positions outside a design row and the later
target variables. It produces a nonzero polynomial in one distinguished
variable with the generator coordinate as a formal root, and retains the
individual degree bound in that variable.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace HittingSet

open MvPolynomial

variable {K α β : Type*} [Field K] {s : ℕ}

/-- The point after the first `k` target coordinates have been replaced by generator outputs. -/
def hybridPoint (g : Fin s → MvPolynomial β K) (k : ℕ)
    (t : β → K) (x : Fin s → K) (j : Fin s) : K :=
  if j.val < k then eval t (g j) else x j

/-- The generator substitution followed by evaluation is the composite point evaluation. -/
theorem eval_substitute (g : α → MvPolynomial β K) (t : β → K) (p : MvPolynomial α K) :
    eval t (aeval g p) = eval (fun j => eval t (g j)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- If full substitution kills the target, a first step kills it at every point. -/
theorem first_vanishing [Infinite K] {p : MvPolynomial (Fin s) K} (hp : p ≠ 0)
    {g : Fin s → MvPolynomial β K} (hg : aeval g p = 0) :
    ∃ i : Fin s, (∃ t x, eval (hybridPoint g i.val t x) p ≠ 0) ∧
      ∀ t x, eval (hybridPoint g (i.val + 1) t x) p = 0 := by
  classical
  let dead (k : ℕ) := ∀ t x, eval (hybridPoint g k t x) p = 0
  have hs : dead s := by
    intro t x
    have h : hybridPoint g s t x = fun j => eval t (g j) := by funext j; simp [hybridPoint]
    rw [h, ← eval_substitute, hg, map_zero]
  have h0 : ¬ dead 0 := by
    intro h
    apply hp
    apply MvPolynomial.funext
    intro x
    have hx : hybridPoint g 0 0 x = x := by funext j; simp [hybridPoint]
    rw [map_zero, ← hx]
    exact h 0 x
  have hex : ∃ k, dead k := ⟨s, hs⟩
  have hl := Nat.find_min' hex hs
  have hn := Nat.find_spec hex
  generalize he : Nat.find hex = k at hl hn
  cases k with
  | zero => exact (h0 hn).elim
  | succ i =>
    have hi : ¬ dead i := Nat.find_min hex (by omega)
    unfold dead at hi
    push Not at hi
    exact ⟨⟨i, by omega⟩, by simpa [dead] using hi, hn⟩

/-- Retain the variables of a row as indeterminates and fix every other seed coordinate. -/
noncomputable def seedOnRow (row : α ↪ β) (t : β → K) : β → MvPolynomial α K :=
  Function.extend row X (fun j => C (t j))

/-- Each retained position keeps its original variable. -/
theorem seedOnRow_row (row : α ↪ β) (t : β → K) (a : α) :
    seedOnRow row t (row a) = X a := row.injective.extend_apply ..

/-- Specializing the surviving row to its original values recovers the full seed point. -/
theorem eval_seedOnRow (row : α ↪ β) (t : β → K) (j : β) :
    eval (t ∘ row) (seedOnRow row t j) = t j := by
  classical
  by_cases h : ∃ a, row a = j
  · obtain ⟨a, rfl⟩ := h
    simp [seedOnRow_row]
  · rw [seedOnRow, Function.extend_apply' _ _ _ h, eval_C]

/-- One distinguished target variable stays free while earlier generator outputs are
inserted and later variables are set to constants. -/
noncomputable def hybridCoordinate (i j : Fin s) (v : Fin s → MvPolynomial α K)
    (x : Fin s → K) : Polynomial (MvPolynomial α K) :=
  if j < i then Polynomial.C (v j) else if j = i then Polynomial.X
  else Polynomial.C (C (x j))

/-- The univariate formal polynomial `B(X,Z)` before the first vanishing step. -/
noncomputable def hybridPolynomial (p : MvPolynomial (Fin s) K) (i : Fin s)
    (v : Fin s → MvPolynomial α K) (x : Fin s → K) : Polynomial (MvPolynomial α K) :=
  eval₂ (Polynomial.C.comp C) (fun j => hybridCoordinate i j v x) p

private theorem eval_hybridPolynomial (p : MvPolynomial (Fin s) K) (i : Fin s)
    (v : Fin s → MvPolynomial α K) (x : Fin s → K) (a : α → K) (z : K) :
    Polynomial.eval₂ (eval a) z (hybridPolynomial p i v x) =
      eval (fun j => if j < i then eval a (v j) else if j = i then z else x j) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [hybridPolynomial]
  | add p q hp hq => simpa [hybridPolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p j hp =>
    simp only [hybridPolynomial, eval₂_mul, eval₂_X, Polynomial.eval₂_mul, map_mul, eval_X] at *
    rw [hp]
    by_cases hji : j < i <;> by_cases hje : j = i <;> simp [hybridCoordinate, hji, hje]

/-- Specialization preserves the individual degree bound in the distinguished variable. -/
theorem hybridPolynomial_natDegree_le (p : MvPolynomial (Fin s) K) (i : Fin s)
    (v : Fin s → MvPolynomial α K) (x : Fin s → K) :
    (hybridPolynomial p i v x).natDegree ≤ p.degreeOf i := by
  classical
  unfold hybridPolynomial
  conv_lhs => rw [p.as_sum]
  simp only [eval₂_sum, eval₂_monomial]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply (Polynomial.natDegree_C_mul_le ..).trans
  apply (Polynomial.natDegree_prod_le ..).trans
  calc
    _ ≤ ∑ j, m j * (hybridCoordinate i j v x).natDegree :=
      Finset.sum_le_sum fun _ _ => Polynomial.natDegree_pow_le
    _ = m i := by
      rw [Finset.sum_eq_single i]
      · simp [hybridCoordinate]
      · intro j _ hji
        by_cases hj : j < i <;> simp [hybridCoordinate, hj, hji]
      · simp
    _ ≤ p.degreeOf i := monomial_le_degreeOf i hm

/-- For a row-indexed generator, the specialized polynomial has the original hard
polynomial as a root. The polynomial is nonzero and its degree in the distinguished
variable is at most the corresponding individual degree of the target. -/
theorem hybrid_root [Infinite K] (row : Fin s → α ↪ β) (f : MvPolynomial α K)
    {p : MvPolynomial (Fin s) K} (hp : p ≠ 0)
    (hzero : aeval (fun j => rename (row j) f) p = 0) :
    ∃ (i : Fin s) (t : β → K) (x : Fin s → K),
      let g := fun j => aeval (seedOnRow (row i) t) (rename (row j) f)
      let B := hybridPolynomial p i g x
      B ≠ 0 ∧ Polynomial.eval f B = 0 ∧ B.natDegree ≤ p.degreeOf i := by
  classical
  let G := fun j => rename (row j) f
  obtain ⟨i, ⟨t, x, hbefore⟩, hafter⟩ := first_vanishing hp hzero
  refine ⟨i, t, x, ?_⟩
  let e := seedOnRow (row i) t
  let v := fun j => aeval e (G j)
  let B := hybridPolynomial p i v x
  have vself : v i = f := by
    change aeval e (rename (row i) f) = _
    rw [aeval_rename]
    have he : e ∘ row i = X := funext (seedOnRow_row (row i) t)
    rw [he, aeval_X_left_apply]
  have hv (a : α → K) (j : Fin s) : eval a (v j) = eval (fun l => eval a (e l)) (G j) :=
    eval_substitute ..
  refine ⟨?_, ?_, hybridPolynomial_natDegree_le ..⟩
  · intro hz
    change B = 0 at hz
    have h := eval_hybridPolynomial p i v x (t ∘ row i) (x i)
    change Polynomial.eval₂ _ _ B = _ at h
    rw [hz, Polynomial.eval₂_zero] at h
    apply hbefore
    convert h.symm using 3
    funext j
    rw [hv]
    simp only [e, eval_seedOnRow, hybridPoint, G]
    split_ifs with h1 h2 h3 <;> first | rfl | subst_vars; rfl | exfalso; omega
  · apply MvPolynomial.funext
    intro a
    have h := eval_hybridPolynomial p i v x a (eval a f)
    change Polynomial.eval₂ _ _ B = _ at h
    change (eval a) (Polynomial.eval f B) = (eval a) 0
    rw [map_zero, Polynomial.eval, Polynomial.hom_eval₂, RingHom.comp_id, h]
    have hz := hafter (fun l => eval a (e l)) x
    convert hz using 3
    funext j
    change (if j < i then eval a (v j) else if j = i then eval a f else x j) =
      (if j.val < i.val + 1 then eval (fun l => eval a (e l)) (G j) else x j)
    rw [← hv, ← vself]
    split_ifs with h1 h2 h3 <;> first | rfl | subst_vars; rfl | exfalso; omega

end HittingSet

end BorderVNP
end Computability
end OAI
