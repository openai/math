import OAI.Computability.VPVNP.RAMTapeBoundaryField
import OAI.Computability.VPVNP.RAMTapeBoundaryBits
import OAI.Computability.VPVNP.RAMTapeStackLift

/-!
# The finite control for scanning sorted records and both endpoint fields

At each record the previous and current bit streams pass through the same
five field loops. The saved current bits are restored to the predecessor
stack before the next record. At an outgoing interior edge the right-hand
stream comes from the sent field. A missing edge requires all of its bits
to be zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Boundary

/-- Stack ports for the sorted block, predecessor, sent record, field width, saved bits, and
slot count. -/
inductive Port where
  | block | previous | sent | width | widthBack | saved | slots
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Select an adjacent-row read check or an outgoing-edge equality check. -/
inductive Mode where
  | row | edge
  deriving DecidableEq

instance : Fintype Mode := derive_fintype% _

/-- Control of the boundary pass, carrying accumulated validity through record scans,
restoration, and endpoint checks. -/
inductive Phase where
  | start
  | checkPrev (ok : Bool)
  | keepPrev (ok bit : Bool)
  | next (ok : Bool)
  | field (mode : Mode) (index : Fin 5) (ok : Bool) (phase : Field.State Flags)
  | restoreSlot (mode : Mode) (ok : Bool)
  | putSlot (mode : Mode) (ok bit : Bool)
  | checkSent (ok : Bool)
  | done (ok : Bool)
  deriving Fintype

/-- Assemble the seven boundary stacks from their bit lists. -/
def store (block previous sent width widthBack saved slots : List Bool) : Stacks Port
  | .block => block
  | .previous => previous
  | .sent => sent
  | .width => width
  | .widthBack => widthBack
  | .saved => saved
  | .slots => slots

/-- Route a field scanner to the predecessor on the left and to the block or sent field on the
right according to the mode. -/
def fieldPorts (m : Mode) : Field.Port → Port
  | .width => .width
  | .widthBack => .widthBack
  | .left => .previous
  | .right => if m = .row then .block else .sent
  | .saved => .saved

theorem fieldPorts_injective (m : Mode) : Function.Injective (fieldPorts m) := by
  intro x y he
  cases m <;> cases x <;> cases y <;> simp_all [fieldPorts]

/-- Advance to the next of five fields, or latch the row or edge check and start restoring the
slot. -/
def afterField (m : Mode) (j : Fin 5) (ok : Bool) (f : Flags) : Phase :=
  if h : j.val+1 < 5 then .field m ⟨j.val+1, h⟩ ok (.tick f)
  else .restoreSlot m (ok && if m = .row then checked f else equalChecked f)

/-- Choose one of four fixed controls using the site's endpoint flags.
Neither the width nor the slot count occurs in the control type. -/
def code (hasPredecessor hasSuccessor : Bool) : StackCode Port Phase
  | .start => .goto (if hasPredecessor then .next true else .checkPrev true)
  | .checkPrev ok => .pop .previous fun b ↦ b.elim (.restoreSlot .row ok) (fun x ↦ .keepPrev (ok && !x) x)
  | .keepPrev ok x => .push .saved x (.checkPrev ok)
  | .next ok => .pop .slots fun b ↦ b.elim
      (if hasSuccessor then .field .edge 0 ok (.tick initial) else .checkSent ok)
      (fun _ ↦ .field .row 0 ok (.tick initial))
  | .field m j ok (.done f) => .goto (afterField m j ok f)
  | .field m j ok q => (Field.code (stepField j) q).rename (fieldPorts m) (.field m j ok)
  | .restoreSlot m ok => .pop .saved fun b ↦ b.elim (if m = .row then .next ok else .done ok)
      (fun x ↦ .putSlot m ok x)
  | .putSlot m ok x => .push .previous x (.restoreSlot m ok)
  | .checkSent ok => .pop .sent fun b ↦ b.elim (.done ok) (fun x ↦ .checkSent (ok && !x))
  | .done ok => .halt ok

theorem update_store (b p s w r t n v : List Bool) (k : Port) :
    Function.update (store b p s w r t n) k v = match k with
      | .block => store v p s w r t n
      | .previous => store b v s w r t n
      | .sent => store b p v w r t n
      | .width => store b p s v r t n
      | .widthBack => store b p s w v t n
      | .saved => store b p s w r v n
      | .slots => store b p s w r t v := by
  funext i
  cases k <;> cases i <;> rfl

end RAMTape.Boundary

end VPVNP
end Computability
end OAI
