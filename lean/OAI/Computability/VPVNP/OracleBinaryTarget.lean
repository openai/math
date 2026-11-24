import OAI.Computability.VPVNP.VerifierMachineNetwork
import Mathlib.Data.Nat.Bitwise

/-!
# Comparing a queried exponent against a count register

One static Boolean expression per possible count compares the query's binary
digits with the fixed count. Values exceeding the number of available flags
therefore produce a zero target row and are rejected by the row-count circuit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace OracleBinaryTarget

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

variable {V : Type*} {w : ℕ}

private def mismatch (wire : Fin w → V) (j : ℕ) (i : Fin w) : Expr V :=
  if j.testBit i.val then .not (.input (wire i)) else .input (wire i)

/-- Boolean equality test between the wired binary word and the natural-number target,
returning false when the target exceeds the word's range. -/
def expr (wire : Fin w → V) (j : ℕ) : Expr V :=
  if j < 2 ^ w then .not (Expr.disjoin ((List.finRange w).map (mismatch wire j)))
  else .const false

private theorem mismatch_eval (wire : Fin w → V) (j : ℕ) (i : Fin w) (x : V → Bool) :
    (mismatch wire j i).eval x = true ↔ x (wire i) ≠ j.testBit i.val := by
  cases h : j.testBit i.val <;> cases h' : x (wire i) <;> simp [mismatch, Expr.eval, h, h']

theorem expr_eval (wire : Fin w → V) (j z : ℕ) (hz : z < 2 ^ w) (x : V → Bool)
    (hx : ∀ i, x (wire i) = z.testBit i.val) : (expr wire j).eval x = decide (z = j) := by
  apply Bool.eq_iff_iff.mpr
  by_cases hj : j < 2 ^ w
  · simp only [expr, hj, ite_true, Expr.eval, Bool.not_eq_true', decide_eq_true_eq]
    rw [Bool.eq_false_iff]
    simp only [ne_eq, Expr.eval_disjoin_true, List.mem_map, List.mem_finRange, true_and,
      exists_exists_eq_and, mismatch_eval, not_exists, not_not, hx]
    constructor
    · intro h
      apply Nat.eq_of_testBit_eq
      intro t
      by_cases ht : t < w
      · exact h ⟨t, ht⟩
      · have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (le_of_not_gt ht)
        rw [Nat.testBit_eq_false_of_lt (hz.trans_le hp), Nat.testBit_eq_false_of_lt (hj.trans_le hp)]
    · rintro rfl
      exact fun _ ↦ rfl
  · have hne : z ≠ j := by omega
    simp [expr, hj, hne, Expr.eval]

theorem expr_size_le (wire : Fin w → V) (j : ℕ) : (expr wire j).size ≤ w * 3 + 2 := by
  unfold expr
  split
  · have h := Expr.size_disjoin_le ((List.finRange w).map (mismatch wire j)) 2 (by
      intro e he
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      unfold mismatch
      split <;> simp [Expr.size])
    simp only [List.length_map, List.length_finRange] at h
    change _ + 1 ≤ _
    omega
  · change 1 ≤ _
    omega

end OracleBinaryTarget

end VPVNP
end Computability
end OAI
