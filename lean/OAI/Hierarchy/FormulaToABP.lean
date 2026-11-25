import OAI.Hierarchy.Models
import OAI.Computability.VPVNP.PolynomialBounds

namespace OAI
/-! # From arithmetic formulas to algebraic branching programs

A subtree extends a partially built branching program from a chosen vertex. The new
sink carries the old vertex value times the polynomial of the subtree. Multiplication
therefore composes two extensions in series. Addition and subtraction extend from the
same vertex and join the resulting sinks with two scalar-labelled edges.
-/

namespace Hierarchy
open MvPolynomial Computability.VPVNP
open MatrixMultiplication.Arithmetic
noncomputable section

variable {F : Type*} {σ : Type} [Field F] [Fintype σ]

private def CanExtend (p : MvPolynomial σ F) (budget : ℕ) : Prop :=
  ∀ {n : ℕ} (g : Rows F σ n) (v : Fin n),
    ∃ (m : ℕ) (h : n ≤ m) (out : Rows F σ m) (sink : Fin m),
      (∀ i : Fin n, out.values (i.castLE h) = g.values i) ∧
      out.values sink = g.values v * p ∧
      m + out.edgeCount ≤ n + g.edgeCount + budget

private theorem values_keep {n : ℕ} (g : Rows F σ n) (edges : List (Fin n × Affine F σ))
    (i : Fin n) : (g.snoc edges).values i.castSucc = g.values i := by
  simp [Rows.values]

private theorem extend_leaf (a : Affine F σ) : CanExtend a.polynomial 2 := by
  intro n g v
  let edges := [(v, a)]
  refine ⟨n + 1, Nat.le_succ _, g.snoc edges, Fin.last n, values_keep g edges, ?_, ?_⟩
  · simp [Rows.values, edges]
  · change n + 1 + (g.edgeCount + 1) ≤ n + g.edgeCount + 2
    omega

private theorem extend_parallel {p q : MvPolynomial σ F} {b c : ℕ}
    (lp : CanExtend p b) (rq : CanExtend q c) (t : F) :
    CanExtend (p + q * C t) (b + c + 3) := by
  intro n g v
  obtain ⟨n₁, h₁, g₁, l, keep₁, leftVal, price₁⟩ := lp g v
  obtain ⟨n₂, h₂, g₂, r, keep₂, rightVal, price₂⟩ := rq g₁ (v.castLE h₁)
  let edges : List (Fin n₂ × Affine F σ) :=
    [(l.castLE h₂, .ofScalar 1), (r, .ofScalar t)]
  refine ⟨n₂ + 1, (h₁.trans h₂).trans (Nat.le_succ _), g₂.snoc edges, Fin.last n₂, ?_, ?_, ?_⟩
  · intro i
    exact (values_keep g₂ edges ((i.castLE h₁).castLE h₂)).trans
      ((keep₂ (i.castLE h₁)).trans (keep₁ i))
  · simp [Rows.values, edges, keep₂, leftVal, rightVal, keep₁, mul_add, mul_assoc]
  · change n₂ + 1 + (g₂.edgeCount + 2) ≤ _
    omega

private theorem extend_series {p q : MvPolynomial σ F} {b c : ℕ}
    (lp : CanExtend p b) (rq : CanExtend q c) :
    CanExtend (p * q) (b + c) := by
  intro n g v
  obtain ⟨n₁, h₁, g₁, l, keep₁, leftVal, price₁⟩ := lp g v
  obtain ⟨n₂, h₂, g₂, r, keep₂, rightVal, price₂⟩ := rq g₁ l
  refine ⟨n₂, h₁.trans h₂, g₂, r, ?_, ?_, by omega⟩
  · intro i
    exact (keep₂ (i.castLE h₁)).trans (keep₁ i)
  · rw [rightVal, leftVal, mul_assoc]

private theorem CanExtend.mono {p : MvPolynomial σ F} {b c : ℕ}
    (h : CanExtend p b) (hbc : b ≤ c) : CanExtend p c := by
  intro n g v
  obtain ⟨m, le, out, sink, keep, value, price⟩ := h g v
  exact ⟨m, le, out, sink, keep, value, by omega⟩

private theorem extend_formula (f : Formula F σ) : CanExtend f.polynomial (5 * f.cost + 2) := by
  induction f with
  | constant t =>
    change CanExtend (C t) 2
    intro n g v
    simpa only [Affine.polynomial_ofScalar] using extend_leaf (Affine.ofScalar (σ := σ) t) g v
  | input i =>
    change CanExtend (X i : MvPolynomial σ F) 2
    intro n g v
    simpa only [Affine.polynomial_ofVariable] using extend_leaf (Affine.ofVariable (F := F) i) g v
  | add l r hl hr =>
    have join : CanExtend (Formula.polynomial l + Formula.polynomial r * C (1 : F))
        ((5 * l.cost + 2) + (5 * r.cost + 2) + 3) := extend_parallel hl hr (1 : F)
    simp only [map_one, mul_one] at join
    apply CanExtend.mono join
    simp only [Expression.cost, Nat.mul_add]
    omega
  | sub l r hl hr =>
    have join : CanExtend (Formula.polynomial l + Formula.polynomial r * C (-1 : F))
        ((5 * l.cost + 2) + (5 * r.cost + 2) + 3) := extend_parallel hl hr (-1 : F)
    simp only [map_neg, map_one, mul_neg_one, ← sub_eq_add_neg] at join
    apply CanExtend.mono join
    simp only [Expression.cost, Nat.mul_add]
    omega
  | mul l r hl hr =>
    apply CanExtend.mono (extend_series hl hr)
    simp only [Expression.cost, Nat.mul_add]
    omega

/-- A formula with `s` binary operations has an affine branching program whose number
of vertices plus edges is at most `5s + 3`. -/
theorem Formula.exists_abp (f : Formula F σ) :
    ∃ g : ABP F σ, g.polynomial = f.polynomial ∧ g.size ≤ 5 * f.cost + 3 := by
  obtain ⟨m, _, out, sink, _, value, price⟩ := extend_formula f (.source : Rows F σ 1) 0
  refine ⟨⟨m, out, sink⟩, ?_, ?_⟩
  · simpa [ABP.polynomial, Rows.values] using value
  · change m + out.edgeCount ≤ _
    simp only [Rows.edgeCount] at price
    omega

/-- Polynomial-size arithmetic formulas yield polynomial-size affine branching programs
over every field. -/
theorem isVBP_of_isVF {τ : ℕ → Type} [∀ n, Fintype (τ n)] {p : Family F τ}
    (h : IsVF p) : IsVBP p := by
  classical
  obtain ⟨family, f, computes, bounded⟩ := h
  choose g correct size using fun n => (f n).exists_abp
  exact ⟨family, g, fun n => (correct n).trans (computes n),
    (((PolynomiallyBounded.const 5).mul bounded).add (PolynomiallyBounded.const 3)).of_le size⟩


end
end Hierarchy

end OAI
