import OAI.Computability.BorderVNP.ParseBatchRecordsPacked
import OAI.Computability.BorderVNP.ParseBatchSortCompare

/-!
# A fixed-width Boolean expression for the local field checks

The bounds on the variable set, the state set and the number of layers may be supplied
as fixed words shared by all records. The validity expression is linear in the word width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP.VerifierNetwork BorderVNP.ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin

/-- Word operands used by a local field check, including the fixed bounds. -/
inductive FormatWord
  | parent | layer | split | left | right | position | variables | states | layers | zero
  deriving DecidableEq

instance : Fintype FormatWord := Fintype.ofList
  [.parent, .layer, .split, .left, .right, .position, .variables, .states, .layers, .zero]
  (by intro a; cases a <;> simp)

/-- Two single bits (the production tag and terminal bit) and fixed-width word operands. -/
abbrev FormatPin (w : ℕ) := Bool ⊕ (FormatWord × Fin w)

/-- Read one high-bit-first word. -/
def formatWord {w : ℕ} (z : FormatPin w → Bool) (f : FormatWord) : ℕ :=
  value (fun k => z (.inr (f, k)))

/-- Interpret the eight guessed fields of a local record. -/
def fieldsFromPins {w : ℕ} (z : FormatPin w → Bool) : Fields :=
  ⟨z (.inl false), formatWord z .parent, formatWord z .layer, formatWord z .split,
    formatWord z .left, formatWord z .right, formatWord z .position, z (.inl true)⟩

private def leWord (w : ℕ) (a b : FormatWord) : Expr (FormatPin w) :=
  leExpr (fun i => .inr (a, i)) (fun i => .inr (b, i))

private def ltWord (w : ℕ) (a b : FormatWord) : Expr (FormatPin w) :=
  .not (leWord w b a)

/-- Boolean expression checking precisely the canonical range and unused-field constraints
of `unpack` for a single record. -/
def formatExpr (w : ℕ) : Expr (FormatPin w) :=
  let bin := (ltWord w .layer .layers).and ((ltWord w .split .layer).and
    ((ltWord w .left .states).and ((ltWord w .right .states).and
    ((leWord w .position .zero).and (.not (.input (.inl true)))))))
  let leaf := (ltWord w .position .variables).and ((leWord w .layer .zero).and
    ((leWord w .split .zero).and ((leWord w .left .zero).and (leWord w .right .zero))))
  (ltWord w .parent .states).and (mux (.input (.inl false)) bin leaf)

/-- Exact size of the per-row range and canonical-padding test. -/
theorem formatExpr_size (w : ℕ) : (formatExpr w).size ≤ 165*w + 40 := by
  simp [formatExpr, leWord, ltWord, mux, StatementCircuit.Expr.size, leExpr_size]
  omega

/-- The local bit test accepts precisely when the decoded row is a canonical in-range record. -/
theorem formatExpr_eval {w : ℕ} (z : FormatPin w → Bool) (hzero : formatWord z .zero = 0) :
    (formatExpr w).eval z = true ↔
      ∃ t, unpack (formatWord z .variables) (formatWord z .states) (formatWord z .layers)
        (fieldsFromPins z) = some t := by
  have cmp (a b : FormatWord) : (leWord w a b).eval z = decide (formatWord z a ≤ formatWord z b) :=
    leExpr_eval _ _ _
  rw [← Option.isSome_iff_exists]
  simp only [formatExpr, ltWord, mux_eval, StatementCircuit.Expr.eval, cmp, fieldsFromPins]
  cases z (.inl false) <;> cases z (.inl true) <;>
    simp [hzero, unpack, apply_dite]

end ParseRecords

end BorderVNP
end Computability
end OAI
