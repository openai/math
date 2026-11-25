import OAI.Computability.BorderVNP.CellSparseChecks

/-! # Statically literal repetition counts in a cell descriptor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Each loop count occurs literally in the finite descriptor, including in unchosen branches. -/
def Stmt.LiteralLoops : Stmt → Prop
  | .seq a b => a.LiteralLoops ∧ b.LiteralLoops
  | .loop e b => (∃ k, e = .lit k) ∧ b.LiteralLoops
  | .ifEq _ _ y n => y.LiteralLoops ∧ n.LiteralLoops
  | _ => True

/-- Scanning a finite sequence preserves literal bounds. -/
theorem sequence_literalLoops (ss : List Stmt) (h : ∀ s ∈ ss, s.LiteralLoops) :
    (sequence ss).LiteralLoops := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact ⟨h _ List.mem_cons_self, ih (fun x hx => h x (.tail _ hx))⟩

/-- Emitting a Boolean expression introduces no computed repeat count. -/
theorem Term.emit_literalLoops (t : Term) (d : ℕ) : (t.emit d).LiteralLoops := by
  induction t generalizing d with
  | lit | wire | paramBit => trivial
  | not a ha => simp [emit,Stmt.LiteralLoops,ha,flip]
  | and a b ha hb | or a b ha hb =>
    simp [emit,sequence,Stmt.LiteralLoops,ha,hb,flip]

/-- The final guard instruction introduces no loop. -/
theorem Term.guard_literalLoops (t : Term) : t.guard.LiteralLoops := ⟨t.emit_literalLoops 0,trivial⟩

end CellSparse

end BorderVNP
end Computability
end OAI
