import OAI.Hierarchy.DescentDatedIssuedOrdinalRead
import OAI.Hierarchy.DescentIssuedSerialCap

namespace OAI
/-! Native prior and issued offsets share a single public serial allowance. -/
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
private abbrev volumePorts := OperandMenu.publicPorts (a:=a) u.shape floor u.count u.hub u.g u.Y active reg
local notation "ports" => volumePorts u x₀
variable (values : (volumePorts u x₀).Values a.successor.setup.placement.newHosts a.successor.setup.placement.groups) (digits : (volumePorts u x₀).casts.bits=a.successor.setup.fallbackBits) (lanes : (volumePorts u x₀).casts.lanes=a.successor.setup.lanes)
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

local notation "carried" h:arg k:arg => (C).cable.query (raw h k)
local notation "surcharge" f:arg h:arg k:arg => (C).cable.priceField f (raw h k)
local notation "issued" h:arg k:arg => OperandMenu.queryDigit (a:=a) (carried h k) (rot (C).queryBits 0 h k) (pub (C).queryBits none h k)
local notation "stored" f:arg h:arg k:arg => (((oldCell f h k).val+(surcharge f h k).val+(rot (C).fieldBits (f).succ h k).val+
  (pub (C).fieldBits (some f) h k).val:ℕ) : Cell (C).fieldBits)


open DescentSixParty.Chronology.DatePorts
local notation "A" => (v).receiver
local notation "draws" => (v).renderFromRanks ((v).linkedRankInputs u.sectors ((v).sheetsStart b)) b
local notation "addend" src:arg j:arg h:arg g:arg => (((src j h g).val : Cell u.operand.coeff).val)

private theorem serial_fee_fits {old feeValue count limit bits coeff : ℕ}
    (empty : old=0) (feeBound : feeValue≤limit) (countBound : count≤limit) (room : 2*limit<2^coeff) :
    (((old+feeValue : ℕ) : Cell coeff) % 2^bits).val+count<2^coeff := by
  subst old
  rw [Nat.zero_add,Fin.val_mod,Fin.val_natCast]
  exact (Nat.add_le_add ((Nat.mod_le ..).trans ((Nat.mod_le ..).trans feeBound)) countBound).trans_lt (by omega)

set_option maxHeartbeats 1400000 in
def ordinal_from_volumes (width : (C).queryBits=(v).receiver.queryBits) (pitch : (C).lanes=(v).receiver.lanes) (moved : (C).Moved base (s) name (((C).sources base w (s)).image m) (Ys) signed)
    (marked : (mark).Fits w ((C).casts base) ∧ Source mark hubWord (C).lanes dst)
    (dated : ∀j,(fee j).Fits w ((C).casts base) ∧ Source (fee j) (tickets j) (C).lanes dst)
    (rawFit : (∀i,(u.rawOperands.query i).Fits w ((v).keepBase b)) ∧
      (∀i,(u.rawOperands.kept i).Fits w ((v).keepBase b)))
    (aux : ∀j,((ports).aux j).Fits w base ∧ Source ((ports).aux j) (values.aux j) (ports).casts.lanes m)
    (coords : ∀j x lo,let t:=(ports).coordinates.src (ports).coordinateBase (ports).saved j x lo
      t.Fits w base ∧ Source t (values.coord j x lo) (ports).casts.lanes m)
    (packet : ∀f j x,let t:=(ports).packets.src (ports).packetBase f j x
      t.Fits w (ports).castBase ∧ Source t (values.packet f j x) (ports).casts.lanes ((C).packetMemory base (s) m))
    (live : (active).Fits w base ∧ Source active values.active (ports).casts.lanes m)
    (regs : ∀j,(reg j).Fits w base ∧ Source (reg j) (values.register j) (ports).casts.lanes m)
    (blank : ∀h k,((cfg).oldConfig.header ((cfg).basic ((payload) h k)) 0).val=0 →
      ((cfg).reg ((payload) h k) 1).val=0)
    (label : ∀h k (hv:h.val<U),((cfg).oldConfig.header ((cfg).basic ((payload) h k)) 0).val≠0 →
      ((cfg).reg ((payload) h k) 3).val=((C).placement.shape (name ⟨h.val,hv⟩)).val)
    (two : 2<2^(C).fieldBits)
    (f : Fin 7) (small : 2*(A).candidates<2^(A).queryBits)
    (hShape : (A).hosts=H) (gShape : (A).groups=G)
    (rawSigned : Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
    (previous : ∀j,Source ((v).previous u.operand draws b (ord f) j) (rawSigned j) (A).lanes (u.operandEntry ok actorMem))
    (cableLimit : 1+2*(C).cable.strip≤2*(A).candidates)
    (rotorLimit : ∀h g,((cfg).oldConfig.header ((cfg).basic ((payload) h g)) 0).val≠0 →
      DescentRotorOrientedQuery.stride u.atlas.board (cfg).rotor.depth (cfg).rotor.residual
      (2^(v).middle.rotorBits) (((cfg).reg ((payload) h g)) 0).val≤(A).candidates)
    (publicLimit : ∀h g,carried h g=0 → rot (C).queryBits 0 h g=0→(pub (C).queryBits none h g).val≤2*(A).candidates)
    (volume : ℕ) (space : 2*volume<2^u.operand.coeff)
    (ranked : f=2→∀j h g,addend rawSigned j h g≤volume)
    (carriedVolume : ∀h g,carried h g≠0 → (surcharge 2 h g).val≤volume)
    (rotorVolume : ∀h g,rot (C).queryBits 0 h g≠0 → (rot (C).fieldBits (2:Fin 7).succ h g).val≤volume)
    (publicVolume : ∀h g,pub (C).queryBits none h g≠0 → (pub (C).fieldBits (some 2) h g).val≤volume) :
    OrdinalRead u ok small actorMem (ord f) :=by
  apply u.ordinal_from_tickets ok actorMem x₀ arg node values digits lanes name hostEq groupEq X strips
    signed hubWord tickets width pitch moved marked dated rawFit aux coords packet live regs blank label two
    f small hShape gShape rawSigned previous cableLimit rotorLimit publicLimit
  · intro h g j field hit _ _
    subst f
    have active_ : carried ((h).cast hShape) ((g).cast gShape)≠0:=by
      intro idle
      rw [idle] at hit
      simp at hit
    have tag : ((C).cable.header ((raw) ((h).cast hShape) ((g).cast gShape)) 0).val=1:=by
      by_contra no
      exact active_ ((C).cable.query_none _ ((C).cable.absent _ no))
    have zeroField := (C).assigned_cable_zero hostEq groupEq (s).which X strips u.menu.keep name dateSlot arg node
      ((h).cast hShape) ((g).cast gShape) 2 (by decide) two tag
    have oldZero : (oldCell 2 ((h).cast hShape) ((g).cast gShape)).val=0 := congrArg Fin.val zeroField
    exact serial_fee_fits oldZero (carriedVolume _ _ active_) (ranked rfl j h g) space
  · intro h g j field hit _ _
    subst f
    have active_ : rot (C).queryBits 0 ((h).cast hShape) ((g).cast gShape)≠0:=by
      intro idle
      rw [idle] at hit
      simp at hit
    exact lt_of_le_of_lt (Nat.add_le_add ((Nat.mod_le ..).trans (rotorVolume _ _ active_)) (ranked rfl j h g)) (by omega)
  · intro h g j field hit _ _
    subst f
    have active_ : pub (C).queryBits none ((h).cast hShape) ((g).cast gShape)≠0:=by
      intro idle
      rw [idle] at hit
      simp at hit
    exact lt_of_le_of_lt (Nat.add_le_add ((Nat.mod_le ..).trans (publicVolume _ _ active_)) (ranked rfl j h g)) (by omega)
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
