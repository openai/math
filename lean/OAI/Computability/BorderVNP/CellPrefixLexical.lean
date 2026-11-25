import OAI.Computability.BorderVNP.CellAddressLength
import OAI.Computability.BorderVNP.CellPrefixGenerator
import OAI.Computability.BorderVNP.CellSparseTable

/-! # Lexical indices of prefix counters and Boolean tests

Only de Bruijn counter references occupy unary index fields in the native address
decoder. Literal strides, table dimensions, and absolute bank offsets contribute
zero to this measure.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Largest referenced loop counter index in a Boolean expression. -/
def Term.lexical : Term → ℕ
  | .lit _ => 0
  | .wire a => a.lexical
  | .paramBit a b => max a.lexical b.lexical
  | .not a => a.lexical
  | .and a b | .or a b => max a.lexical b.lexical

/-- The value-stack adjustments inserted by compilation reference no extra lexical counters. -/
@[simp] theorem Term.emit_lexical (a : Term) (tmp : ℕ) : (a.emit tmp).lexical = a.lexical := by
  induction a generalizing tmp <;>
    simp [emit,sequence,flip,Stmt.lexical,lexical,NatExpr.lexical, *]

@[simp] theorem Term.guard_lexical (a : Term) : a.guard.lexical = a.lexical := by simp [guard,Stmt.lexical]
@[simp] theorem Term.sign_lexical (a : Term) : a.sign.lexical = a.lexical := by simp [sign,Stmt.lexical]

@[simp] theorem Term.equal_lexical (a b : Term) : (a.equal b).lexical = max a.lexical b.lexical := by
  simp [equal,lexical]

@[simp] theorem Term.implies_lexical (a b : Term) : (a.implies b).lexical = max a.lexical b.lexical := rfl

/-- A disjunction uses precisely the counters available to its components. -/
theorem Term.any_lexical_le (as : List Term) {k : ℕ} (h : ∀ a ∈ as, a.lexical ≤ k) : (Term.any as).lexical ≤ k := by
  induction as with
  | nil => exact Nat.zero_le _
  | cons a as ih => exact max_le (h _ List.mem_cons_self) (ih (fun t ht => h _ (.tail _ ht)))

/-- Entering one additional loop raises referenced indices by at most one. -/
theorem NatExpr.weaken_lexical_le (a : NatExpr) : a.weaken.lexical ≤ a.lexical+1 := by
  induction a <;> simp only [weaken,lexical,max_le_iff] <;> omega

theorem Term.weaken_lexical_le (a : Term) : a.weaken.lexical ≤ a.lexical+1 := by
  induction a with
  | lit _ => exact Nat.zero_le _
  | wire a => exact a.weaken_lexical_le
  | paramBit a b =>
    simp only [weaken,lexical,max_le_iff]
    have := a.weaken_lexical_le; have := b.weaken_lexical_le; omega
  | not _ ih => exact ih
  | and a b iha ihb | or a b iha ihb => simp only [weaken,lexical,max_le_iff]; omega

@[simp] theorem Port.expr_lexical (p : Port) (i k : NatExpr) : (p.expr i k).lexical = max i.lexical k.lexical := by
  simp [expr,NatExpr.lexical]

/-- A word equality against a static number mentions only its bit-address counters. -/
theorem wordIs_lexical_le (as : List NatExpr) (j : ℕ) {k : ℕ} (h : ∀ a ∈ as, a.lexical ≤ k) :
    (wordIs as j).lexical ≤ k := by
  induction as generalizing j with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    simp only [wordIs,Term.equal_lexical,Term.lexical,max_zero,max_le_iff]
    exact ⟨h _ List.mem_cons_self, ih _ (fun t ht => h _ (.tail _ ht))⟩

namespace Prefix

@[simp] theorem flagTerm_lexical (base cap : ℕ) (i k : NatExpr) :
    (flagTerm base cap i k).lexical = max i.lexical k.lexical := by simp [flagTerm,Term.lexical,NatExpr.lexical]

/-- Initializing a prefix table only refers to the innermost candidate counter. -/
@[simp] theorem initGen_lexical (base cap : ℕ) : (initGen base cap).lexical = 0 := by
  simp [initGen,Stmt.lexical,NatExpr.lexical,Term.lexical]

/-- One row check embeds the caller's copy expression and predicate under a single fresh candidate loop. -/
theorem stepGen_lexical_le (base cap : ℕ) (i : NatExpr) (m : Term) :
    (stepGen base cap i m).lexical ≤ max i.lexical m.lexical + 1 := by
  simp only [stepGen,Stmt.lexical,NatExpr.lexical,Term.guard_lexical, rowTest,Term.equal_lexical,
    Term.lexical,flagTerm_lexical,zero_max,max_zero,max_le_iff]
  have := i.weaken_lexical_le
  have := m.weaken_lexical_le
  omega

/-- A complete prefix table only needs one index beyond those used by its match expression. -/
theorem generator_lexical_le (base copies cap : ℕ) (m : NatExpr → Term) :
    (generator base copies cap m).lexical ≤ (m (.index 0)).lexical+1 := by
  simpa [generator,Stmt.lexical,NatExpr.lexical] using stepGen_lexical_le base cap (.index 0) (m (.index 0))

end Prefix
end CellSparse

end BorderVNP
end Computability
end OAI
