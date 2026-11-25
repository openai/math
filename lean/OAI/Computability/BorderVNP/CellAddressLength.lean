import OAI.Computability.BorderVNP.CellBranchDispatch
import OAI.Computability.BorderVNP.CellCompactSize

/-! # Length of padded binary address descriptors

Address literals occupy binary fields and de Bruijn indices occupy unary fields. The bound
therefore measures the numerical magnitude of a lexical index separately from the binary
length of an arbitrary literal. Padding depends only on the fixed arithmetic depth.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- The largest lexical index stored as a unary field of an address expression. -/
def NatExpr.lexical : NatExpr → ℕ
  | .lit _ => 0
  | .index i => i
  | .add a b | .mul a b | .sub a b => max a.lexical b.lexical

/-- The largest lexical index referenced anywhere in a compact command tree. -/
def Stmt.lexical : Stmt → ℕ
  | .nil | .fixed _ => 0
  | .read a => a.lexical
  | .bit a b => max a.lexical b.lexical
  | .seq s t => max s.lexical t.lexical
  | .loop a s => max a.lexical s.lexical
  | .ifEq a b s t => max (max a.lexical b.lexical) (max s.lexical t.lexical)

/-- Sequencing arbitrarily many commands with bounded lexical indices preserves the bound. -/
theorem sequence_lexical_le (xs : List Stmt) {k : ℕ} (h : ∀ s ∈ xs, s.lexical ≤ k) :
    (sequence xs).lexical ≤ k := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons s xs ih => exact max_le (h _ List.mem_cons_self) (ih (fun t ht => h _ (.tail _ ht)))

end CellSparse

namespace CellMacro.Address

open CellSparse RationalHitting.StackLanguage
open private fields children from OAI.Computability.BorderVNP.CellAddressEvaluator

private theorem header_length (e : NatExpr) :
    (Coding.code (fields e)).length ≤ 10 + 2*e.field.size + e.lexical := by
  have hb (b : Bool) : (Coding.code b).length = 1 := rfl
  cases e <;> simp [fields, NatExpr.field, NatExpr.lexical, hb, ← Nat.size_eq_bits_len] <;> omega

private theorem bounds_children (e : NatExpr) :
    ((children e).1.field ≤ e.field ∧ (children e).1.lexical ≤ e.lexical) ∧
    ((children e).2.field ≤ e.field ∧ (children e).2.lexical ≤ e.lexical) := by
  cases e <;> simp [children, NatExpr.field, NatExpr.lexical]

private theorem pack_length_rec (d : ℕ) (e : NatExpr) (M J : ℕ) (he : e.field ≤ M) (hj : e.lexical ≤ J) :
    (Coding.code (pack d e)).length ≤ 64^(d+1)*(1+M.size+J) := by
  have hu := (header_length e).trans (show 10+2*e.field.size+e.lexical ≤ 10+2*M.size+J by
    have := Nat.size_le_size he; omega)
  induction d generalizing e with
  | zero => change (Coding.code (fields e)).length ≤ 64*(1+M.size+J); omega
  | succ d ih =>
    obtain ⟨⟨fl,jl⟩,fr,jr⟩ := bounds_children e
    have hl := ih (children e).1 (fl.trans he) (jl.trans hj) ((header_length _).trans (by
      have := Nat.size_le_size (fl.trans he); omega))
    have hr := ih (children e).2 (fr.trans he) (jr.trans hj) ((header_length _).trans (by
      have := Nat.size_le_size (fr.trans he); omega))
    change (Coding.code (fields e, pack d (children e).1, pack d (children e).2)).length ≤ _
    simp only [prod_code_length] at hu
    simp only [prod_code_length, pow_succ (64 : ℕ) (d+1)]
    have hp : 1 ≤ 64^(d+1) := Nat.one_le_pow _ _ (by decide)
    have hbase := Nat.mul_le_mul_right (1+M.size+J) hp
    rw [Nat.one_mul] at hbase
    rw [Nat.mul_right_comm (64^(d+1)) 64 (1+M.size+J)]
    omega

/-- Fixed-depth encoding size is linear in the binary literal width and numerical
lexical index. Both children, including the zero padding at leaves, are accounted for. -/
theorem pack_length (d : ℕ) (e : NatExpr) :
    (Coding.code (pack d e)).length ≤ 64^(d+1)*(1+e.field.size+e.lexical) :=
  pack_length_rec d e _ _ le_rfl le_rfl

end CellMacro.Address

namespace CellMacro.Generator

open CellSparse

/-- Testing equality does not increase the largest referenced lexical index. -/
@[simp] theorem difference_lexical (a b : NatExpr) :
    (difference a b).lexical = max a.lexical b.lexical := by simp [difference, NatExpr.lexical, max_comm]

/-- Testing equality preserves the largest numerical field. -/
@[simp] theorem difference_field (a b : NatExpr) :
    (difference a b).field = max a.field b.field := by simp [difference, NatExpr.field, max_comm]

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
