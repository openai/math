import OAI.Computability.VPVNP.VerifierMachineNetwork

/-!
# Boolean comparators for the batched parse table

A record is compared by reading its bits most significant first. The code of
a tuple of fields is their concatenation in sort-key order. The first unequal
bit decides the order, including the tag and request-number tie breakers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchSort

open VPVNP.VerifierNetwork

/-- Numeric value of a fixed-width binary record with most significant bit first. -/
def value : {w : ℕ} → (Fin w → Bool) → ℕ
  | 0, _ => 0
  | w + 1, x => (x 0).toNat * 2 ^ w + value (fun i => x i.succ)

/-- All fixed-width records fit in the corresponding range of natural numbers. -/
theorem value_lt {w : ℕ} (x : Fin w → Bool) : value x < 2 ^ w := by
  induction w with
  | zero => simp [value]
  | succ w ih =>
    have h := ih (fun i => x i.succ)
    cases hx : x 0 <;> simp only [value, hx, Bool.toNat_false, Bool.toNat_true,
      zero_mul, one_mul, zero_add, pow_succ] <;> omega

/-- Numeric sorting retains all bits, including fields used to break equal-key ties. -/
theorem value_injective (w : ℕ) : Function.Injective (@value w) := by
  induction w with
  | zero => exact fun _ _ _ => Subsingleton.elim ..
  | succ w ih =>
    intro x y h
    have hx := value_lt (fun i : Fin w => x i.succ)
    have hy := value_lt (fun i : Fin w => y i.succ)
    have hheads : x 0 = y 0 := by
      cases h₀ : x 0 <;> cases h₁ : y 0 <;> simp_all [value]
      omega
    have ht : (fun i : Fin w => x i.succ) = (fun i : Fin w => y i.succ) := by
      apply ih
      simpa only [value, hheads, Nat.add_right_inj] using h
    funext i
    exact Fin.cases hheads (fun j => congrFun ht j) i

private def sameBit {ι : Type*} (a b : Expr ι) : Expr ι :=
  .or (.and a b) (.and (.not a) (.not b))

/-- Boolean expression comparing the two complete records. The recursive comparison
occurs only once in each bit's expression. -/
def leExpr {ι : Type*} : {w : ℕ} → (Fin w → ι) → (Fin w → ι) → Expr ι
  | 0, _, _ => .const true
  | _ + 1, x, y =>
    let a : Expr ι := .input (x 0)
    let b : Expr ι := .input (y 0)
    .or (.and (.not a) b) (.and (sameBit a b) (leExpr (fun i => x i.succ) (fun i => y i.succ)))

/-- Comparison costs a linear number of AND/OR/NOT expression nodes. -/
theorem leExpr_size {ι : Type*} {w : ℕ} (x y : Fin w → ι) :
    (leExpr x y).size = 15 * w + 1 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [leExpr, sameBit, BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.size,
      ih, Nat.mul_succ]
    omega

/-- Evaluating the comparison gives the exact numerical order of the bit records. -/
theorem leExpr_eval {ι : Type*} {w : ℕ} (x y : Fin w → ι) (z : ι → Bool) :
    (leExpr x y).eval z = decide (value (z ∘ x) ≤ value (z ∘ y)) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have hx := value_lt (fun i : Fin w => z (x i.succ))
    have hy := value_lt (fun i : Fin w => z (y i.succ))
    cases ax : z (x 0) <;> cases ay : z (y 0) <;>
      simp [leExpr, sameBit, BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval,
        ax, ay, ih, value, Function.comp_def] <;> omega

/-- Multiplexer over expressions. -/
def mux {ι : Type*} (flag yes no : Expr ι) : Expr ι :=
  .or (.and flag yes) (.and (.not flag) no)

/-- The two alternative fields of a multiplexer are selected by the comparator's decision. -/
theorem mux_eval {ι : Type*} (flag yes no : Expr ι) (x : ι → Bool) :
    (mux flag yes no).eval x = if flag.eval x then yes.eval x else no.eval x := by
  cases h : flag.eval x <;>
    simp [mux, BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval, h]

end ParseBatchSort

end BorderVNP
end Computability
end OAI
