import OAI.Hierarchy.DescentDatedOperandOrdinalFields
import OAI.Hierarchy.DescentNamedOperandComplete
import OAI.Hierarchy.DescentDatedPublicValues

namespace OAI
/-! Read the actually issued query and retained value at a single seven-field output ordinal. -/
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
private abbrev ordinalPorts := OperandMenu.publicPorts (a:=a) u.shape floor u.count u.hub u.g u.Y active reg
local notation "ports" => ordinalPorts u x₀
variable (values : (ordinalPorts u x₀).Values a.successor.setup.placement.newHosts a.successor.setup.placement.groups) (digits : (ordinalPorts u x₀).casts.bits=a.successor.setup.fallbackBits) (lanes : (ordinalPorts u x₀).casts.lanes=a.successor.setup.lanes)
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

private theorem source_width {bits bits' H' G' lanes₀ : ℕ} (same : bits=bits')
    (e : Expr) (f : Fin H'→Fin G'→Cell bits) (mem : Memory w) (h : Source e f lanes₀ mem) :
    Source e (fun j g=>(f j g).cast (congrArg (2^·) same)) lanes₀ mem:=by
  subst bits'
  exact h

include lanes in
theorem issued_ordinal (width : (C).queryBits=(v).receiver.queryBits) (pitch : (C).lanes=(v).receiver.lanes) (moved : (C).Moved base (s) name (((C).sources base w (s)).image m) (Ys) signed)
    (marked : (mark).Fits w ((C).casts base) ∧ Source mark hubWord (C).lanes dst)
    (dated : ∀j,(fee j).Fits w ((C).casts base) ∧ Source (fee j) (tickets j) (C).lanes dst)
    (rawFit : (∀i,(u.rawOperands.query i).Fits w ((v).keepBase b)) ∧
      (∀i,(u.rawOperands.kept i).Fits w ((v).keepBase b)))
    (aux : ∀j,((ports).aux j).Fits w base ∧ Source ((ports).aux j) (values.aux j) (ports).casts.lanes m)
    (coords : ∀j sample lo,let t:=(ports).coordinates.src (ports).coordinateBase (ports).saved j sample lo
      t.Fits w base ∧ Source t (values.coord j sample lo) (ports).casts.lanes m)
    (packet : ∀f j sample,let t:=(ports).packets.src (ports).packetBase f j sample
      t.Fits w (ports).castBase ∧ Source t (values.packet f j sample) (ports).casts.lanes ((C).packetMemory base (s) m))
    (live : (active).Fits w base ∧ Source active values.active (ports).casts.lanes m)
    (regs : ∀j,(reg j).Fits w base ∧ Source (reg j) (values.register j) (ports).casts.lanes m)
    (blank : ∀h k,((cfg).oldConfig.header ((cfg).basic ((payload) h k)) 0).val=0 →
      ((cfg).reg ((payload) h k) 1).val=0)
    (label : ∀h k (hv:h.val<U),((cfg).oldConfig.header ((cfg).basic ((payload) h k)) 0).val≠0 →
      ((cfg).reg ((payload) h k) 3).val=((C).placement.shape (name ⟨h.val,hv⟩)).val)
    (two : 2<2^(C).fieldBits) :
    ∀f : Fin 7,
    Source (u.operand.query (ord f)) (fun h k=>(OperandMenu.queryDigit (a:=a) ((C).cable.query ((raw) h k))
      (rot (C).queryBits 0 h k) (pub (C).queryBits none h k)).cast (congrArg (2^·) width)) (v).receiver.lanes (u.operandEntry ok actorMem) ∧
    Source (u.operand.kept (ord f)) (fun h k=>
      ((((oldCell f h k).val+((C).cable.priceField f ((raw) h k)).val+
        (rot (C).fieldBits f.succ h k).val+(pub (C).fieldBits (some f) h k).val:ℕ) :
        Cell (C).fieldBits).val:Cell (v).receiver.valueBits)) (v).receiver.lanes (u.operandEntry ok actorMem):=by
  have order:=(v).operand_order b
  have roof:=((v).keep_before b).trans_lt (((order.1.trans order.2).trans ((v).final_ge b)).trans_lt ok.full)
  have columns:=u.menu.request_columns u.shape floor u.count u.hub u.g u.Y active reg m values digits lanes
     dateSlot arg node name hostEq groupEq X strips signed hubWord tickets ok.placed roof moved
     mark fee marked dated aux coords packet live regs blank label two
  intro f
  have q:=source_width width _ _ _ columns.1
  have kept:=columns.2 f
  rw [pitch] at q kept
  exact u.operand_ordinal_fields f arg x₀ node ok actorMem _ _ (rawFit.1 (ord f)) (rawFit.2 (ord f)) q kept

include lanes in
/-- Read all seven ordinals from the retained archive and the published input rows at this date. -/
theorem issued_public_ordinal (width : (C).queryBits=(v).receiver.queryBits) (pitch : (C).lanes=(v).receiver.lanes) (moved : (C).Moved base (s) name (((C).sources base w (s)).image m) (Ys) signed)
    (marked : (mark).Fits w ((C).casts base) ∧ Source mark hubWord (C).lanes dst)
    (dated : ∀j,(fee j).Fits w ((C).casts base) ∧ Source (fee j) (tickets j) (C).lanes dst)
    (rawFit : (∀i,(u.rawOperands.query i).Fits w ((v).keepBase b)) ∧
      (∀i,(u.rawOperands.kept i).Fits w ((v).keepBase b)))
    (publicRead : u.PublicValuesRead ok actorMem dateSlot digits name values)
    (two : 2<2^(C).fieldBits) :
    ∀f : Fin 7,
    Source (u.operand.query (ord f)) (fun h k=>(OperandMenu.queryDigit (a:=a) ((C).cable.query ((raw) h k))
      (rot (C).queryBits 0 h k) (pub (C).queryBits none h k)).cast (congrArg (2^·) width)) (v).receiver.lanes (u.operandEntry ok actorMem) ∧
    Source (u.operand.kept (ord f)) (fun h k=>
      ((((oldCell f h k).val+((C).cable.priceField f ((raw) h k)).val+
        (rot (C).fieldBits f.succ h k).val+(pub (C).fieldBits (some f) h k).val:ℕ) :
        Cell (C).fieldBits).val:Cell (v).receiver.valueBits)) (v).receiver.lanes (u.operandEntry ok actorMem):=by
  obtain ⟨aux,coords,packet,live,regs,blank,label⟩:=publicRead
  exact u.issued_ordinal ok actorMem x₀ arg node values digits lanes name hostEq groupEq X strips signed
    hubWord tickets width pitch moved marked dated rawFit aux coords packet live regs blank label two

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
