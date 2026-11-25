import OAI.Hierarchy.DescentDatedIssuedRoles
import OAI.Hierarchy.DescentIssuedFreshChoice

namespace OAI
/-! # The posted public or rotor digit at its actual saved coefficient width -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentPackedZip
open scoped Fin.CommRing
noncomputable section
theorem lower_value {s b : ℕ} (amount : ℕ) (room : s≤b) :
    (((amount:Cell b).val:ℕ):Cell s)=(amount:Cell s) :=by
  apply Fin.ext
  change amount%2^b%2^s=amount%2^s
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow _ room)

theorem lower_column {n d : ℕ} (board : NonlinearExpanders.Graph n d) (C : Config) {s b : ℕ}
    (room : s≤b) (field : Option (Fin 7)) (j : Fin C.oldConfig.mouths) (x : C.Data n) :
    ((C.column board b field j x).val:Cell s)=C.column board s field j x :=by
  unfold column
  dsimp only
  split
  · simp
  · cases field <;> apply lower_value _ room
end
end Hierarchy.DescentResetPublicOperandBook.Config

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
theorem issued_public_at (h : Fin H) (g : Fin G) {out : ℕ×ℕ×ℕ×Bool}
    (hit : (cfg).mixed u.atlas.board node.val arg.val ((payload) h g)=some out)
    (present : pub (C).queryBits none h g≠0) (enough : (v).receiver.valueBits≤(C).fieldBits) :
    issued h g=pub (C).queryBits none h g ∧
    ∀f : Fin 7,((stored f h g).val:Cell (v).receiver.valueBits)=pub (v).receiver.valueBits (some f) h g :=by
  have tag : (C).cable.header ((raw) h g) 0=
      ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch u.menu.keep name (Ys)
        ((R).outputID 0 0 arg node) dateSlot h g).val:Cell (C).fieldBits):=rfl
  have primary : u.bank.primary=u.menu.keep := rfl
  have indices : (finProdFinEquiv.symm at_ : Fin (cfg).args×Fin (cfg).nodes)=(arg,node):=Equiv.symm_apply_apply _ _
  obtain ⟨query,valueFields⟩:=u.menu.issued_fresh_public name ((payload) h g) at_ hostEq groupEq X strips (s).which
    dateSlot arg node h g ((raw) h g) tag (blank h g) (label h g) (by simpa only [indices,primary] using hit) present
  refine ⟨by simpa only [indices,primary] using query,fun f=>?_⟩
  have compared :=congrArg (fun t : Cell (C).fieldBits=>(t.val:Cell (v).receiver.valueBits)) (valueFields f)
  refine Eq.trans ?_ (DescentResetPublicOperandBook.Config.lower_column u.atlas.board (cfg) enough (some f) at_ ((payload) h g))
  simpa only [indices,primary] using compared

include lanes blank label in
omit lanes in
theorem issued_rotor_at (h : Fin H) (g : Fin G)
    (present : rot (C).queryBits 0 h g≠0) (enough : (v).receiver.valueBits≤(C).fieldBits) :
    issued h g=rot (C).queryBits 0 h g ∧
    ∀f : Fin 7,((stored f h g).val:Cell (v).receiver.valueBits)=rot (v).receiver.valueBits f.succ h g :=by
  have tag : (C).cable.header ((raw) h g) 0=
      ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch u.menu.keep name (Ys)
        ((R).outputID 0 0 arg node) dateSlot h g).val:Cell (C).fieldBits):=rfl
  have primary : u.bank.primary=u.menu.keep := rfl
  have indices : (finProdFinEquiv.symm at_ : Fin (cfg).args×Fin (cfg).nodes)=(arg,node):=Equiv.symm_apply_apply _ _
  obtain ⟨query,valueFields⟩:=u.menu.issued_fresh_rotor name ((payload) h g) at_ hostEq groupEq X strips (s).which
    dateSlot arg node h g ((raw) h g) tag (blank h g) (label h g) (by simpa only [indices,primary] using present)
  refine ⟨by simpa only [indices,primary] using query,fun f=>?_⟩
  have compared:=congrArg (fun t : Cell (C).fieldBits=>(t.val:Cell (v).receiver.valueBits)) (valueFields f)
  simpa only [indices,primary,DescentResetPublicOperandBook.Config.lower_value _ enough] using compared

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
