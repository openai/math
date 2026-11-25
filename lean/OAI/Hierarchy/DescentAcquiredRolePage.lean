import OAI.Hierarchy.DescentArchiveCellRead
import OAI.Hierarchy.DescentNodeCellRolePage
import OAI.Hierarchy.DescentOrdinaryHostPad

namespace OAI
/-! # Recovering the signed primitive-token row on the compact ordinary host prefix -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentCompiler DescentKernelHistory DescentPrimitivePalette
open DescentLocalArchiveOrder DescentSIMDLookup DescentColonies
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {clock : AtomSchedule} {k i z D wire hist s Z : ℕ}
  (r : Reached W G q ε clock k i z D wire hist) (arch : BitDescription W) (number : Local arch)
  (ports : DatePorts) (room : RangeRoom ports r arch) (op : RotorSpec)
  (labels : NodeOrder.All arch→Label G s Z op)

theorem original_tokens_positive (y : NodeOrder.All arch) : token G s Z op (labels y)≠0:=by
  intro eqn
  have value:=congrArg Fin.val eqn
  change ((codec (G:=G) op).store (labels y)).val+1=0 at value
  omega

/-- Changing the host rectangle preserves the original node found at a common address. -/
theorem slot_at_host {H : ℕ} (b : Block k) (j : Fin ports.nodes) (h : Fin H)
    (g : Fin (clock.groupCount i)) (inside : h.val<ports.operandHosts) :
    slotAt ports r arch number room (b.cast (congrArg (2^·) room.radix)) j
      ⟨h.val,inside⟩ (g.cast room.groups)=Reached.NodeCells.atPhysical r arch number b j h g:=by
  simp only [slotAt,Fin.cast_cast,Fin.cast_refl,Reached.NodeCells.atPhysical,id_eq]

/-- Host padding copies every original one-based token before counting the nodes.
The underlying value is also exact at a hole of an occupied host. -/
theorem acquired_role_page {H width : ℕ} (enough : Fintype.card r.V≤ports.operandHosts)
    (wide : Fintype.card r.V≤H)
    (roles : Block k→Fin ports.operandHosts→Fin ports.venue.groups→Cell (width*ports.nodes))
    (published : ∀b h g,(roles b h g).val=(encode (printedBits G s Z op) ports.nodes (fun n=>
      (slotAt ports r arch number room (b.cast (congrArg (2^·) room.radix)) n h g).elim 0
        (fun y=>token G s Z op (labels y)))).val)
    (b : Block k) (h : Fin (Fintype.card r.V)) (g : Fin (clock.groupCount i)) :
    (DescentOrdinaryHostPad.extend H (roles b) (h.castLE wide) (g.cast room.groups)).val=
      (Reached.NodeCells.rolePage (N:=ports.nodes) r arch number (fun y=>token G s Z op (labels y)) b h g).val:=by
  have inside : (h.castLE wide).val<ports.operandHosts:=h.isLt.trans_le enough
  rw [DescentOrdinaryHostPad.extend,dite_eq_left inside,published]
  simp only [Reached.NodeCells.rolePage,slot_at_host]
  rfl

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
