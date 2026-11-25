import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Recognizing native opcode tables of parametrized assembly fragments -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- Syntactic test for a program containing only native tags, allowing both alternatives of
a binary guess and excluding the separate sign and private-call tags. -/
def Code.nativeOnly : Code → Bool
  | .call .. | .sign .. => false
  | .seq a b | .choose a b | .ifLt _ _ a b | .ifEq _ _ a b => a.nativeOnly && b.nativeOnly
  | .whileLt _ _ a => a.nativeOnly
  | _ => true

/-- Every unsigned choice-free program consists of native tags. -/
theorem Code.nativeOnly_of_unsigned (c : Code) (h : c.unsigned = true) : c.nativeOnly = true := by
  induction c <;> simp_all [Code.unsigned,Code.nativeOnly,Bool.and_eq_true]

private theorem emit_tag (c : Code) (ok : c.nativeOnly = true) {p : ℕ} (lab : ℕ → Fin p) (pc a b : ℕ) :
    (c.emit lab pc a b).2 = .native := by
  induction c generalizing a b with
  | seq l r ih ih' | ifEq _ _ l r ih ih' | ifLt _ _ l r ih ih' | choose l r ih ih' =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp ok
    simp only [Code.emit]
    repeat' split
    all_goals first | rfl | exact ih hl .. | exact ih' hr ..
  | whileLt _ _ body ih =>
    simp only [Code.emit]
    split
    · rfl
    · exact ih ok ..
  | _ => first | rfl | contradiction

/-- Every emitted PC, including the fall-through halt, has the ordinary native tag. -/
theorem Code.program_tag_native (c : Code) (ok : c.nativeOnly = true) (pc : Fin (c.slots+1)) :
    c.program.tag pc = .native := by
  change (c.row pc).2 = _
  rw [Code.row]
  split
  · exact emit_tag c ok ..
  · rfl

end RoutingISA

end BorderVNP
end Computability
end OAI
