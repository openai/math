import OAI.Computability.VPVNP.RAMTapeSortRowPorts
import OAI.Computability.VPVNP.RAMTapeSortField

/-!
# Register layout and outcomes for a physical compare-exchange row

A local partner is fetched from the current block. At a cross-site layer
the outgoing block is compared with the site’s current records and the
incoming partner record supplies the other comparator operand. The flags
are retained in reverse chronological order, just as the output records are.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRow

open RAMBoundary Boundary

/-- Source of the right comparison operand, either the fetched local partner, the outgoing
record, or the incoming record. -/
inductive RightSource | localRegister | outgoing | incoming
  deriving DecidableEq

/-- Select the row stack holding the right operand for this source. -/
def RightSource.port : RightSource → Port
  | .localRegister => .right
  | .outgoing => .crossSend
  | .incoming => .crossReceive

/-- Wire a record comparator into the row stacks, sending its output to the next block and its
validity bit to the flags stack. -/
def comparePorts (src : RightSource) : Sorter.Port → Port
  | .left => .left
  | .right => src.port
  | .width => .width
  | .widthBack => .widthBack
  | .savedLeft => .savedLeft
  | .savedRight => .savedRight
  | .tmp => .selectTmp
  | .next => .next
  | .valid => .flags

theorem comparePorts_injective (src : RightSource) : Function.Injective (comparePorts src) := by
  cases src <;> decide

variable {w B : ℕ}

/-- Choose the smaller or larger raw record according to the comparator orientation, choosing
the first on a minimum tie and the second on a maximum tie. -/
def chosen (keepMin : Bool) (a b : RawSlot w) : RawSlot w :=
  if Sorter.leDecision (Sorter.expected a b) == keepMin then a else b

/-- Test that both raw slots have canonical record tags. -/
def selectOK (a b : RawSlot w) : Bool :=
  Sorter.canonical (fun i => SuccessorTags.Tag.ofNat (a i).val) &&
    Sorter.canonical (fun i => SuccessorTags.Tag.ofNat (b i).val)

/-- Test canonicality of both slots and equality according to the record comparator. -/
def verifyOK (a b : RawSlot w) : Bool := selectOK a b && Sorter.equalDecision (Sorter.expected a b)

/-- All sources of a prepared row except the two cross-site streams. -/
structure Ready (s : Stacks Port) (block : Fin B → RawSlot w) (i j : Fin B)
    (localStride keepMin : Bool) : Prop extends FetchReady w s where
  block_eq : s .current = blockBytes (List.ofFn block)
  row_eq : s .row = List.replicate i.val true
  partner_eq : s .partner = List.replicate j.val true
  orientation : s .orientation = [keepMin]
  localFlag : s .localFlag = [localStride]
  left : s .left = []
  right : s .right = []
  savedLeft : s .savedLeft = []
  savedRight : s .savedRight = []
  selectTmp : s .selectTmp = []

/-- Terminal register values of one row. A cross-site row pushes its verify
flag first and its select flag second. -/
def result (s : Stacks Port) (keepMin : Bool) (a b : RawSlot w)
    (sent : Option (RawSlot w)) (sendTail receiveTail : List Bool) : Stacks Port
  | .partner | .orientation | .localFlag => []
  | .next => (recordBytes (chosen keepMin a b)).reverse ++ s .next
  | .flags => selectOK a b :: (sent.elim (s .flags) (fun x => verifyOK a x :: s .flags))
  | .crossSend => sendTail
  | .crossReceive => receiveTail
  | p => s p

end RAMTape.SortRow

end VPVNP
end Computability
end OAI
