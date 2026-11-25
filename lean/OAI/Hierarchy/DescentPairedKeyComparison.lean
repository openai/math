import OAI.Hierarchy.ProtocolRAMCheapCode
import Mathlib.Data.Nat.Pairing

namespace OAI
/-! # Comparing the implemented fallback names with no wide products -/

namespace Hierarchy.DescentPairedKeyComparison
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM.DescriptorExpr
open scoped Fin.CommRing

def tailLT (a b c d : ℕ) : Prop :=
  if a<b then (if c<d then a<c else True) else (if c<d then False else b<d)

def ordered (a b c d : ℕ) : Prop :=
  max a b< max c d ∨ max a b=max c d ∧ tailLT a b c d

private theorem square_le (a b : ℕ) : (max a b)^2≤Nat.pair a b := by
  exact (Nat.le_add_right _ _).trans (Nat.max_sq_add_min_le_pair a b)

private theorem pair_order {a b c d : ℕ} (lt : max a b< max c d) : Nat.pair a b<Nat.pair c d :=
  (Nat.pair_lt_max_add_one_sq _ _).trans_le
    ((Nat.pow_le_pow_left lt 2).trans (square_le ..))

theorem pair_iff (a b c d : ℕ) : Nat.pair a b<Nat.pair c d ↔ ordered a b c d := by
  unfold ordered
  rcases lt_trichotomy (max a b) (max c d) with lt|eqn|gt
  · exact iff_of_true (pair_order lt) (.inl lt)
  · have tied : (max a b < max c d ∨ max a b = max c d ∧ tailLT a b c d) ↔ tailLT a b c d := by
      simp [eqn]
    rw [tied]
    by_cases ab : a<b <;> by_cases cd : c<d
    · simp only [max_eq_right ab.le,max_eq_right cd.le] at eqn
      subst d
      simp [Nat.pair,tailLT,ab,cd]
    · simp only [max_eq_right ab.le,max_eq_left (le_of_not_gt cd)] at eqn
      subst c
      simp [Nat.pair,tailLT,ab,cd]; omega
    · simp only [max_eq_left (le_of_not_gt ab),max_eq_right cd.le] at eqn
      subst d
      simp [Nat.pair,tailLT,ab,cd]; omega
    · simp only [max_eq_left (le_of_not_gt ab),max_eq_left (le_of_not_gt cd)] at eqn
      subst c
      simp [Nat.pair,tailLT,ab,cd]
  · simp [not_lt_of_gt gt,ne_of_gt gt,not_lt_of_gt (pair_order gt)]

def high (x y : Expr) : Expr := .branch .lt x y y x

def tail (a b c d yes no : Expr) : Expr :=
  .branch .lt a b (.branch .lt c d (.branch .lt a c yes no) yes)
    (.branch .lt c d no (.branch .lt b d yes no))

def earlier (a b c d yes no : Expr) : Expr :=
  let l:=high a b
  let r:=high c d
  .branch .lt l r yes (.branch .eq l r (tail a b c d yes no) no)

variable {w : ℕ}
private theorem branch_lt (x y t f : Expr) (m : Memory w) (r : Word w) :
    (Expr.branch .lt x y t f).eval m r =
      if (x.eval m r).val < (y.eval m r).val then t.eval m r else f.eval m r := by
  simp only [Expr.eval, Comparison.test, decide_eq_true_eq, Fin.lt_def]

private theorem branch_eq (x y t f : Expr) (m : Memory w) (r : Word w) :
    (Expr.branch .eq x y t f).eval m r =
      if (x.eval m r).val = (y.eval m r).val then t.eval m r else f.eval m r := by
  simp only [Expr.eval, Comparison.test, beq_iff_eq, Fin.ext_iff]

private theorem high_val (x y : Expr) (m : Memory w) (r : Word w) :
    ((high x y).eval m r).val = max (x.eval m r).val (y.eval m r).val := by
  by_cases h : (x.eval m r).val < (y.eval m r).val
  · simp only [high, branch_lt, ite_eq_left h, max_eq_right h.le]
  · simp only [high, branch_lt, ite_eq_right h, max_eq_left (Nat.le_of_not_gt h)]

open Classical in
private theorem tail_eval (a b c d yes no : Expr) (m : Memory w) (r : Word w) :
    (tail a b c d yes no).eval m r =
      if tailLT (a.eval m r).val (b.eval m r).val (c.eval m r).val (d.eval m r).val
      then yes.eval m r else no.eval m r := by
  classical
  by_cases ab : (a.eval m r).val < (b.eval m r).val <;>
    by_cases cd : (c.eval m r).val < (d.eval m r).val <;>
    simp [tail, branch_lt, tailLT, ab, cd]

theorem earlier_eval (a b c d yes no : Expr) (m : Memory w) (r : Word w) :
    (earlier a b c d yes no).eval m r=
      if Nat.pair (a.eval m r).val (b.eval m r).val<Nat.pair (c.eval m r).val (d.eval m r).val
      then yes.eval m r else no.eval m r := by
  classical
  simp only [earlier, branch_lt, branch_eq, high_val, tail_eval, pair_iff, ordered]
  by_cases smaller : max (a.eval m r).val (b.eval m r).val < max (c.eval m r).val (d.eval m r).val
  · simp [smaller]
  · by_cases equal : max (a.eval m r).val (b.eval m r).val = max (c.eval m r).val (d.eval m r).val
    · simp [equal]
    · simp [smaller, equal]

end Hierarchy.DescentPairedKeyComparison

end OAI
