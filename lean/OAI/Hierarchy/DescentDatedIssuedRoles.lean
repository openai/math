import OAI.Hierarchy.DescentDatedIssuedOperands
import OAI.Hierarchy.DescentIssuedRoleChoice
import OAI.Hierarchy.DescentIssuedHeadZeros

namespace OAI
/-! The source of every ordinal and the source of its kept field at the actual reset receiver. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSIMDLookup DescentResetOperandSetup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
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
private abbrev rolePorts := OperandMenu.publicPorts (a:=a) u.shape floor u.count u.hub u.g u.Y active reg
local notation "ports" => rolePorts u x₀
variable (values : (rolePorts u x₀).Values a.successor.setup.placement.newHosts a.successor.setup.placement.groups) (digits : (rolePorts u x₀).casts.bits=a.successor.setup.fallbackBits) (lanes : (rolePorts u x₀).casts.lanes=a.successor.setup.lanes)
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

include lanes blank label in
omit lanes in
theorem issued_role_all (h : Fin H) (g : Fin G) :
    (issued h g=carried h g ∧ ∀f,stored f h g=((oldCell f h g).val+(surcharge f h g).val:ℕ)) ∨
    (issued h g=rot (C).queryBits 0 h g ∧ ∀f,stored f h g=rot (C).fieldBits f.succ h g) ∨
    (issued h g=pub (C).queryBits none h g ∧ ∀f,stored f h g=pub (C).fieldBits (some f) h g) :=by
  have tag : (C).cable.header ((raw) h g) 0=
      ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch u.menu.keep name (Ys)
        ((R).outputID 0 0 arg node) dateSlot h g).val:Cell (C).fieldBits):=rfl
  have primary : u.bank.primary=u.menu.keep := rfl
  have indices : (finProdFinEquiv.symm at_ : Fin (cfg).args×Fin (cfg).nodes)=(arg,node):=Equiv.symm_apply_apply _ _
  simpa only [indices,primary] using u.menu.issued_owner_all name ((payload) h g) at_ hostEq groupEq X strips (s).which
    dateSlot arg node h g ((raw) h g) tag (blank h g) (label h g)

include blank label in
theorem issued_role_at (f : Fin 7) (h : Fin H) (g : Fin G) :
    (issued h g=carried h g ∧ stored f h g=((oldCell f h g).val+(surcharge f h g).val:ℕ)) ∨
    (issued h g=rot (C).queryBits 0 h g ∧ stored f h g=rot (C).fieldBits f.succ h g) ∨
    (issued h g=pub (C).queryBits none h g ∧ stored f h g=pub (C).fieldBits (some f) h g) :=by
  have tag : (C).cable.header ((raw) h g) 0=
      ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch u.menu.keep name (Ys)
        ((R).outputID 0 0 arg node) dateSlot h g).val:Cell (C).fieldBits):=rfl
  have primary : u.bank.primary=u.menu.keep := rfl
  have indices : (finProdFinEquiv.symm at_ : Fin (cfg).args×Fin (cfg).nodes)=(arg,node):=Equiv.symm_apply_apply _ _
  simpa only [indices,primary] using u.menu.issued_owner name ((payload) h g) at_ hostEq groupEq X strips (s).which
    dateSlot arg node h g ((raw) h g) tag (blank h g) (label h g) f

include blank label in
/-- At a positive request, an outgoing kind or neighbor never retains a positive summand. -/
theorem issued_head_zero (f : Fin 7) (h : Fin H) (g : Fin G)
    (bits : 2<2^(C).fieldBits) (early : f.val<2) (hit : issued h g≠0) :
    stored f h g=0:=by
  have order:=u.issued_role_at x₀ arg node values digits name hostEq groupEq X strips signed hubWord tickets
      blank label f h g
  rcases order with ⟨qeq,field⟩|⟨_,field⟩|⟨_,field⟩
  · have active_ : carried h g≠0:=qeq ▸ hit
    have tag : ((C).cable.header ((raw) h g) 0).val=1:=by
      by_contra no
      exact active_ ((C).cable.query_none _ ((C).cable.absent _ no))
    have old := (C).assigned_cable_zero hostEq groupEq (s).which X strips u.menu.keep name dateSlot arg node h g f
      (by omega) bits tag
    have z₂ : f≠2:=by intro e;subst f;exact (by decide : ¬((2:Fin 7).val<2)) early
    have z₃ : f≠3:=by intro e;subst f;exact (by decide : ¬((3:Fin 7).val<2)) early
    change oldCell f h g=0 at old
    rw [field,old]
    simp [DescentResetRetainedCableLaw.Shape.priceField,z₂,z₃]
  · rw [field]
    have no := (cfg).rotor.flat_head_zero u.atlas.board (cfg).multiplicity (cfg).grain (cfg).split
      node.val arg.val ((cfg).reg ((payload) h g)) f early
    exact congrArg (fun value : ℕ => (value : Cell (C).fieldBits)) no
  · rw [field]
    exact (cfg).public_head_zero u.atlas.board (C).fieldBits at_ ((payload) h g) f early

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
