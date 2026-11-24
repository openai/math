import OAI.Computability.VPVNP.UniversalMachine
import Mathlib.Tactic.Linarith

/-!
# Length of a literal coefficient-machine program

There are nine table rows per running state, each with at most two transition
records. A unary target takes at most one bit per state including the halting
states. This gives a quadratic bound for the self-delimiting program prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

private theorem unary_length (k : ℕ) : (unary k).length = k + 1 := by simp [unary]

private theorem instructionBits_length_le {extra : ℕ} (a : Instruction extra) :
    ((instructionFields a).flatMap unary).length ≤ extra + 14 := by
  simp only [instructionFields, List.flatMap_cons, List.flatMap_nil, List.length_append,
    unary_length, List.length_nil]
  have := a.target.isLt
  have := a.firstSymbol.isLt
  have := a.secondSymbol.isLt
  have := a.firstMove.isLt
  have := a.secondMove.isLt
  omega

private theorem branchBits_length_le {extra : ℕ} (b : Branches extra) :
    ((branchFields b).flatMap unary).length ≤ 2 * extra + 31 := by
  cases b with
  | stop => simp [branchFields, unary_length]
  | one a =>
    simp only [branchFields, List.flatMap_cons, List.length_append, unary_length]
    have := instructionBits_length_le a
    omega
  | two a b =>
    simp only [branchFields, List.flatMap_cons, List.flatMap_append, List.length_append,
      unary_length]
    have := instructionBits_length_le a
    have := instructionBits_length_le b
    omega

private theorem rowsBits_length_le {extra : ℕ} (rows : List (Branches extra)) :
    ((rows.flatMap branchFields).flatMap unary).length ≤ rows.length * (2 * extra + 31) := by
  induction rows with
  | nil => simp
  | cons b rows ih =>
    simp only [List.flatMap_cons, List.flatMap_append, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    exact (Nat.add_le_add (branchBits_length_le b) ih).trans_eq (Nat.add_comm ..)

/-- Including its unary length header, a literal table has polynomial size in its state count. -/
theorem programPrefix_length_le (p : Program) :
    (programPrefix p).length ≤ 1000 * (p.extra + 1) ^ 2 := by
  have hrows := rowsBits_length_le p.rows
  rw [p.rows_length] at hrows
  simp only [programPrefix, List.length_append, unary_length, tableBits]
  split
  · simp_all
  · simp only [List.flatMap_cons, List.length_append, unary_length]
    have hsub : p.extra - 1 + 1 = p.extra := by omega
    rw [hsub]
    nlinarith [Nat.zero_le (p.extra ^ 2)]

end UniversalMachine

end VPVNP
end Computability
end OAI
