import OAI.Hierarchy.DescentDatedIssuedRoles
import OAI.Hierarchy.DescentResetAssignedKind
import OAI.Hierarchy.DescentNextSignedRAM
import OAI.Hierarchy.DescentDatedOperandTagRead

namespace OAI
/-! # The reset menu emits a valid physical pointer kind at every operand socket -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSIMDLookup DescentResetOperandSetup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 900000
variable {a : PhysicalReset} {floor w U : ℕ} (u : a.DateInputs floor w) (ok : u.Ready) (actorMem : Memory w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "base" => (v).operandFloor b
local notation "C" => (v).setup
local notation "R" => (C).retained
local notation "H" => (C).placement.newHosts
local notation "G" => (C).placement.groups
local notation "m" => u.beforeSetupImage ok actorMem
local notation "cfg" => publicOperands u.atlas u.roots u.menu.payload
variable (x₀ : Fin a.successor.receiver.blocks) (arg : Fin a.successor.setup.retained.args) (node : Fin a.successor.setup.retained.nodes)
local notation "dateSlot" => x₀.cast u.operandBlocks
local notation "ctrl" => (v).controlRegisters
local notation "start" => (v).controlFloor b
local notation "actor" => (v).actor
local notation "origin" => (v).middle.stop b
local notation "active" => (ctrl).live start (dateSlot).val
local notation "reg" => (ctrl).ports start (a.c/2) (dateSlot).val ((actor).directory origin).inverse
    ((actor).depths origin) ((actor).levels origin)
private abbrev kindPorts := OperandMenu.publicPorts (a:=a) u.shape floor u.count u.hub u.g u.Y active reg
local notation "ports" => kindPorts u x₀
variable (values : (kindPorts u x₀).Values a.successor.setup.placement.newHosts a.successor.setup.placement.groups) (digits : (kindPorts u x₀).casts.bits=a.successor.setup.fallbackBits) (lanes : (kindPorts u x₀).casts.lanes=a.successor.setup.lanes)
variable (name : Fin U→Fin a.successor.setup.placement.sparse)
variable (hostEq : a.successor.setup.placement.oldHosts=a.successor.setup.retained.hosts) (groupEq : a.successor.setup.placement.groups*a.successor.setup.placement.blocks=a.successor.setup.retained.grouped)
variable (X : a.successor.setup.seven.Packets) (strips : a.successor.setup.retained.Strips)
local notation "s" => u.bank
local notation "Ys" => (C).assignedDigits hostEq groupEq (s).which X strips
variable (signed : Fin a.successor.setup.strip→Fin a.successor.setup.placement.oldHosts→Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.signedBits)
variable (hubWord : Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→Cell a.successor.setup.fieldBits) (tickets : Fin a.successor.setup.strip→Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→Cell a.successor.setup.fieldBits)
local notation "raw" => (C).carriedRow (s) name (Ys) signed dateSlot arg node hubWord tickets
local notation "payload" => u.menu.publicData u.shape floor u.count u.hub u.g u.Y active reg values digits (dateSlot).val
local notation "at_" => (finProdFinEquiv (arg,node) : Fin (C).members)
local notation "dst" => ((C).code base w (s) u.laws).image m
local notation "oldCell" f:arg h:arg k:arg => ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  (s).primary name (Ys) ((R).outputID 1 f arg node) dateSlot h k).val : Cell (C).fieldBits)
local notation "rot" width:arg f:arg h:arg k:arg => ((cfg).rotor.flatReg u.atlas.board (cfg).multiplicity (cfg).grain (cfg).split
   node.val arg.val f ((cfg).reg ((payload) h k)) : Cell width)
local notation "pub" width:arg f:arg h:arg k:arg => (cfg).column u.atlas.board width f at_ ((payload) h k)
local notation "mark" => (v).retainedHub b dateSlot
local notation "fee" => (v).retainedTicket b dateSlot
local notation "ord" f:arg => (v).operandOrdinal u.operand f arg x₀ node

private abbrev roleOperandData := payload
variable (blank : ∀ (h : Fin a.successor.setup.placement.newHosts) (k : Fin a.successor.setup.placement.groups),((publicOperands u.atlas u.roots u.menu.payload).oldConfig.header ((publicOperands u.atlas u.roots u.menu.payload).basic ((roleOperandData u x₀ values digits) h k)) 0).val=0 →
    ((publicOperands u.atlas u.roots u.menu.payload).reg ((roleOperandData u x₀ values digits) h k) 1).val=0)
variable (label : ∀ (h : Fin a.successor.setup.placement.newHosts) (k : Fin a.successor.setup.placement.groups) (hv:h.val<U),((publicOperands u.atlas u.roots u.menu.payload).oldConfig.header ((publicOperands u.atlas u.roots u.menu.payload).basic ((roleOperandData u x₀ values digits) h k)) 0).val≠0 →
    ((publicOperands u.atlas u.roots u.menu.payload).reg ((roleOperandData u x₀ values digits) h k) 3).val=(a.successor.setup.placement.shape (name ⟨h.val,hv⟩)).val)
local notation "carried" h:arg k:arg => (C).cable.query ((raw) h k)
local notation "surcharge" f:arg h:arg k:arg => (C).cable.priceField f ((raw) h k)
local notation "issued" h:arg k:arg => OperandMenu.queryDigit (a:=a) (carried h k) (rot (C).queryBits 0 h k) (pub (C).queryBits none h k)
local notation "stored" f:arg h:arg k:arg => (((oldCell f h k).val+(surcharge f h k).val+(rot (C).fieldBits (f).succ h k).val+
  (pub (C).fieldBits (some f) h k).val:ℕ) : Cell (C).fieldBits)

include blank label in
theorem issued_tag_le (h : Fin H) (g : Fin G) :
    (stored (0 : Fin 7) h g).val ≤ 2 := by
  obtain choice := u.issued_role_all x₀ arg node values digits name hostEq groupEq X strips
    signed hubWord tickets blank label h g
  rcases choice with ⟨_,same⟩ | ⟨_,same⟩ | ⟨_,same⟩
  · rw [same 0]
    have rawBound := (C).assigned_tag_le hostEq groupEq (s).which X strips (s).primary name dateSlot arg node h g
    have retained : (oldCell (0 : Fin 7) h g).val ≤ 2 := (Nat.mod_le ..).trans rawBound
    simpa [DescentResetRetainedCableLaw.Shape.priceField] using
      ((Nat.mod_le (oldCell (0 : Fin 7) h g).val (2^(C).fieldBits)).trans retained)
  · rw [same 0]
    have zero := (cfg).rotor.flat_head_zero u.atlas.board (cfg).multiplicity (cfg).grain (cfg).split
      node.val arg.val ((cfg).reg ((payload) h g)) (0 : Fin 7) (by decide)
    have cleared : rot (C).fieldBits (0 : Fin 7).succ h g = 0 :=
      congrArg (fun t : ℕ => (t : Cell (C).fieldBits)) zero
    exact (congrArg Fin.val cleared).trans_le (by simp)
  · rw [same 0, (cfg).public_head_zero u.atlas.board (C).fieldBits at_ ((payload) h g) (0 : Fin 7) (by decide)]
    simp only [Fin.val_zero, Nat.zero_le]

include blank label in
/-- The actual held digit plus the flag of the ranked signed candidate has a legal kind.
A nonzero issue clears the held head, even when the selected candidate is absent. -/
theorem issued_ranked_tag {D cap signedBits coeff : ℕ} (h : Fin H) (g : Fin G)
    (bits : 2 < 2^(C).fieldBits) (pick : Option (DescentNextSignedWindow.Record D cap))
    (idle : issued h g = 0 → pick = none) :
    ((stored (0 : Fin 7) h g).val : Cell coeff).val +
      (((DescentNextSignedWindow.Native.fields pick 0 : Cell signedBits).val : Cell coeff)).val ≤ 2 := by
  by_cases zero : issued h g = 0
  · rw [idle zero]
    simpa [DescentNextSignedWindow.Native.fields] using
      ((Nat.mod_le (stored (0 : Fin 7) h g).val (2^coeff)).trans
        (u.issued_tag_le x₀ arg node values digits name hostEq groupEq X strips signed hubWord tickets blank label h g))
  · have clear := u.issued_head_zero x₀ arg node values digits name hostEq groupEq X strips
      signed hubWord tickets blank label 0 h g bits (by decide) zero
    rw [clear]
    have bound : DescentNextSignedWindow.Native.fields pick 0 ≤ 1 := by cases pick <;> simp [DescentNextSignedWindow.Native.fields]
    have aux := (Nat.mod_le (DescentNextSignedWindow.Native.fields pick 0) (2^signedBits)).trans bound
    have final := (Nat.mod_le ((DescentNextSignedWindow.Native.fields pick 0)%2^signedBits) (2^coeff)).trans aux
    simpa only [Fin.val_zero,Nat.cast_zero,Fin.val_natCast,Nat.zero_add] using final.trans (by decide : 1 ≤ 2)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
