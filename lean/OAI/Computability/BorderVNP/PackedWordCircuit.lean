import OAI.Computability.BorderVNP.CrossingParallelFrame
import OAI.Computability.BorderVNP.ParseBatchWordArithmetic
import OAI.Computability.BorderVNP.ParseBatchVerifierCountWords
import OAI.Computability.VPVNP.VerifierMachineSplice

/-! # Shared Boolean circuits for public width calculations

Widths and interval offsets in §§6–7 are binary words. This compiler supplies the local
arithmetic of the sparse descriptor pass. Each occurrence of an operation contributes a
quadratic number of Boolean gates in the word length and reads its inputs by gate references.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Word

open VPVNP.VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin

/-- Width operations used to delimit the selected prefix and retain both unused pieces. -/
inductive Op where
  | add | sub | minimum | maximum
  deriving DecidableEq

/-- Numerical semantics; subtraction saturates at zero. -/
def Op.apply : Op → ℕ → ℕ → ℕ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .minimum => min
  | .maximum => max

private def formula (w : ℕ) (op : Op) (j : Fin w) : Expr (Fin w ⊕ Fin w) :=
  let a := fun i => StatementCircuit.Expr.input (.inl i)
  let b := fun i => StatementCircuit.Expr.input (.inr i)
  match op with
  | .add => addWord a b j
  | .sub => mux (leExpr Sum.inr Sum.inl) (subWord a b j) (.const false)
  | .minimum => mux (leExpr Sum.inl Sum.inr) (a j) (b j)
  | .maximum => mux (leExpr Sum.inl Sum.inr) (b j) (a j)

private theorem zero_value (w : ℕ) : value (fun _ : Fin w => false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simpa only [value, Bool.toNat_false, zero_mul, zero_add] using ih

private theorem eval_formula (w : ℕ) (op : Op) (x : Fin w ⊕ Fin w → Bool)
    (fits : op.apply (value (x ∘ Sum.inl)) (value (x ∘ Sum.inr)) < 2^w) :
    value (fun j => (formula w op j).eval x) =
      op.apply (value (x ∘ Sum.inl)) (value (x ∘ Sum.inr)) := by
  let a : Fin w → Expr (Fin w ⊕ Fin w) := fun i => .input (.inl i)
  let b : Fin w → Expr (Fin w ⊕ Fin w) := fun i => .input (.inr i)
  cases op with
  | add => exact addWord_value x a b fits
  | sub =>
    by_cases h : value (x ∘ Sum.inr) ≤ value (x ∘ Sum.inl)
    · simp only [Op.apply, formula, mux_eval, leExpr_eval, h, decide_true, ite_true]
      exact subWord_value x a b h
    · simp only [formula, mux_eval, leExpr_eval, h, decide_false, Bool.false_eq_true, ite_false,
        StatementCircuit.Expr.eval, zero_value, Op.apply, Nat.sub_eq_zero_of_le (le_of_not_ge h)]
  | minimum =>
    by_cases h : value (x ∘ Sum.inl) ≤ value (x ∘ Sum.inr)
    · simp only [formula, mux_eval, leExpr_eval, h, decide_true, ite_true, StatementCircuit.Expr.eval,
        Op.apply, min_eq_left h]; rfl
    · simp only [formula, mux_eval, leExpr_eval, h, decide_false, Bool.false_eq_true, ite_false,
        StatementCircuit.Expr.eval, Op.apply, min_eq_right (le_of_not_ge h)]; rfl
  | maximum =>
    by_cases h : value (x ∘ Sum.inl) ≤ value (x ∘ Sum.inr)
    · simp only [formula, mux_eval, leExpr_eval, h, decide_true, ite_true, StatementCircuit.Expr.eval,
        Op.apply, max_eq_right h]; rfl
    · simp only [formula, mux_eval, leExpr_eval, h, decide_false, Bool.false_eq_true, ite_false,
        StatementCircuit.Expr.eval, Op.apply, max_eq_left (le_of_not_ge h)]; rfl

private theorem formula_size (w : ℕ) (op : Op) (j : Fin w) :
    (formula w op j).size ≤ 100 * (w + 1) := by
  let a : Fin w → Expr (Fin w ⊕ Fin w) := fun i => .input (.inl i)
  let b : Fin w → Expr (Fin w ⊕ Fin w) := fun i => .input (.inr i)
  have ha (i : Fin w) : (a i).size ≤ 1 := le_rfl
  have hb (i : Fin w) : (b i).size ≤ 1 := le_rfl
  have hsum := sumWord_size_le false a b 1 ha hb j
  have hsub := subWord_size_le a b 1 ha hb j
  cases op <;> simp only [formula, addWord, mux, StatementCircuit.Expr.size, leExpr_size] <;>
    dsimp [a,b] at hsum hsub <;> omega

/-- A straight-line formula on binary descriptor fields. -/
inductive WidthExpr (I : Type*) where
  | field (i : I)
  | const (n : ℕ)
  | binary (op : Op) (a b : WidthExpr I)

namespace WidthExpr

variable {I : Type*}

/-- Unbounded natural-number value of a descriptor expression. -/
def eval (x : I → ℕ) : WidthExpr I → ℕ
  | .field i => x i
  | .const n => n
  | .binary op a b => op.apply (a.eval x) (b.eval x)

/-- Every intermediate result fits the installed binary word width. -/
def Fits (w : ℕ) (x : I → ℕ) : WidthExpr I → Prop
  | .field i => x i < 2^w
  | .const n => n < 2^w
  | .binary op a b => a.Fits w x ∧ b.Fits w x ∧ op.apply (a.eval x) (b.eval x) < 2^w

/-- Number of nodes of the descriptor expression. -/
def nodes : WidthExpr I → ℕ
  | .field _ | .const _ => 1
  | .binary _ a b => a.nodes + b.nodes + 1

variable [Fintype I]

/-- Actual AND/OR/NOT gate fragment exposing the word at its output pins. -/
noncomputable def frame (w : ℕ) : WidthExpr I → Frame (I × Fin w) (Fin w)
  | .field i => Frame.initial (fun j => (i,j))
  | .const n => (Frame.initial (id : I × Fin w → _)).step (fun j =>
      .const ((ParseBatchCounts.numberWords w).symm ⟨n % 2^w, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ j))
  | .binary op a b => (Crossing.parallelFrame (frame w a) (frame w b)).step (formula w op)

/-- The evaluator implements natural-number arithmetic on every well-sized record. -/
theorem frame_value (w : ℕ) (e : WidthExpr I) (x : I × Fin w → Bool)
    (h : e.Fits w (fun i => value (fun j => x (i,j)))) :
    value (fun j => (e.frame w).eval x j) = e.eval (fun i => value (fun j => x (i,j))) := by
  induction e with
  | field i => simp [frame, eval]
  | const n =>
    change n < 2^w at h
    simp only [frame, Frame.step_eval, StatementCircuit.Expr.eval, eval]
    exact (ParseBatchCounts.value_encode (w := w) ⟨n % 2^w, Nat.mod_lt _ (Nat.two_pow_pos _)⟩).trans (Nat.mod_eq_of_lt h)
  | binary op a b ia ib =>
    obtain ⟨ha,hb,hop⟩ := h
    let z := (Crossing.parallelFrame (frame w a) (frame w b)).eval x
    have hleft : value (z ∘ Sum.inl) = a.eval (fun i => value (fun j => x (i,j))) := by
      simpa [z,Function.comp_def] using ia ha
    have hright : value (z ∘ Sum.inr) = b.eval (fun i => value (fun j => x (i,j))) := by
      simpa [z,Function.comp_def] using ib hb
    have hbound : op.apply (value (z ∘ Sum.inl)) (value (z ∘ Sum.inr)) < 2^w := by
      rwa [hleft,hright]
    simpa only [frame, Frame.step_eval, eval, ← hleft, ← hright] using eval_formula w op z hbound

/-- The size depends on the number of static arithmetic operations and word bits, regardless
of the widths that the public records represent. -/
theorem frame_size (w : ℕ) (e : WidthExpr I) :
    (e.frame w).size ≤ e.nodes * (100 * (w+1)^2) := by
  induction e with
  | field i => simp [frame]
  | const n =>
    have h := Frame.step_size_le (Frame.initial (id : I × Fin w → _))
      (fun j => StatementCircuit.Expr.const ((ParseBatchCounts.numberWords w).symm ⟨n%2^w, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ j))
      1 (fun _ => le_rfl)
    simp only [Frame.initial_size, Fintype.card_fin, zero_add, mul_one] at h
    exact h.trans (by simp [nodes]; nlinarith)
  | binary op a b ia ib =>
    have h := Frame.step_size_le (Crossing.parallelFrame (frame w a) (frame w b)) (formula w op)
      (100*(w+1)) (formula_size w op)
    simp only [Crossing.parallelFrame_size, Fintype.card_fin] at h
    change ((Crossing.parallelFrame (a.frame w) (b.frame w)).step (formula w op)).size ≤ _
    apply h.trans
    simp only [nodes, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (Nat.add_le_add ia ib) (by nlinarith)

end WidthExpr
end Packing.Word

end BorderVNP
end Computability
end OAI
