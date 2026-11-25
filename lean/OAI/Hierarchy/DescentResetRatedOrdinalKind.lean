import OAI.Hierarchy.DescentResetIssuedKind
import OAI.Hierarchy.DescentDatedIssuedOrdinalRead

namespace OAI
/-! # A physically read reset tag from the actual ordinal and ranked candidate -/
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
private abbrev ticketPorts := OperandMenu.publicPorts (a:=a) u.shape floor u.count u.hub u.g u.Y active reg
local notation "ports" => ticketPorts u x₀
variable (values : (ticketPorts u x₀).Values a.successor.setup.placement.newHosts a.successor.setup.placement.groups) (digits : (ticketPorts u x₀).casts.bits=a.successor.setup.fallbackBits) (lanes : (ticketPorts u x₀).casts.lanes=a.successor.setup.lanes)
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

private theorem cast_grid {hostCount groupCount rows cols bits width : ℕ} (he : rows=hostCount) (ge : cols=groupCount)
    (e : Expr) (table : Fin hostCount→Fin groupCount→Cell bits) (lanes : ℕ) (mem : Memory width)
    (reads : Source e table lanes mem) :
    Source e (fun h g=>table (h.cast he) (g.cast ge)) lanes mem:=by
  subst rows
  subst cols
  exact reads

open DescentOperandCandidateLookup
include lanes in
set_option maxHeartbeats 1000000 in
theorem ranked_tag_ordinal (width : (C).queryBits=(v).receiver.queryBits) (pitch : (C).lanes=(v).receiver.lanes) (moved : (C).Moved base (s) name (((C).sources base w (s)).image m) (Ys) signed)
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
    (small : 2*(A).candidates<2^(A).queryBits)
    (hShape : (A).hosts=H) (gShape : (A).groups=G)
    {D cap : ℕ} (ranked : Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Option (DescentNextSignedWindow.Record D cap))
    (previous : ∀j,Source ((v).previous u.operand draws b (ord 0) j)
      (fun h g=>(DescentNextSignedWindow.Native.fields (ranked j h g) 0 : Cell (A).signedBits))
      (A).lanes (u.operandEntry ok actorMem))
    (cableLimit : 1+2*(C).cable.strip≤2*(A).candidates)
    (rotorLimit : ∀h g,((cfg).oldConfig.header ((cfg).basic ((payload) h g)) 0).val≠0 →
      DescentRotorOrientedQuery.stride u.atlas.board (cfg).rotor.depth (cfg).rotor.residual
      (2^(v).middle.rotorBits) (((cfg).reg ((payload) h g)) 0).val≤(A).candidates)
    (publicLimit : ∀h g,carried h g=0 → rot (C).queryBits 0 h g=0 → (pub (C).queryBits none h g).val≤2*(A).candidates)
    (coeffRoom : 2 < 2^u.operand.coeff) :
    ∃r : OrdinalRead u ok small actorMem (ord 0), ∀h g,
      (r.kept h g).val+(DescentOperandCandidateLookup.selected r.query (fun j h g=>((r.raw j h g).val:Cell u.operand.coeff)) h g).val ≤ 2 :=by
  let requests (h : Fin (A).hosts) (g : Fin (A).groups) := (issued ((h).cast hShape) ((g).cast gShape)).cast (congrArg (2^·) width)
  let kept (h : Fin (A).hosts) (g : Fin (A).groups) := ((stored (0 : Fin 7) ((h).cast hShape) ((g).cast gShape)).val:Cell u.operand.coeff)
  have actual:=u.issued_ordinal ok actorMem x₀ arg node values digits lanes name hostEq groupEq X strips
    signed hubWord tickets width pitch moved marked dated rawFit aux coords packet live regs blank label two 0
  have qread : Source (u.operand.query (ord 0)) requests (A).lanes (u.operandEntry ok actorMem):=
    cast_grid hShape gShape (u.operand.query (ord 0)) (fun h g => (issued h g).cast (congrArg (2^·) width))
      (A).lanes (u.operandEntry ok actorMem) actual.1
  have kread : Source (u.operand.kept (ord 0)) kept (A).lanes (u.operandEntry ok actorMem):=
    cast_grid hShape gShape (u.operand.kept (ord 0)) (fun h g => ((stored (0 : Fin 7) h g).val : Cell u.operand.coeff))
      (A).lanes (u.operandEntry ok actorMem) actual.2
  have bounded (h : Fin (A).hosts) (g : Fin (A).groups) : (requests h g).val≤2*(A).candidates:=by
    change (issued ((h).cast hShape) ((g).cast gShape)).val≤2*(A).candidates
    apply OperandMenu.queryDigit_le
    · exact ((C).cable.query_le _).trans cableLimit
    · intro _
      by_cases occupied : ((cfg).oldConfig.header ((cfg).basic ((payload) ((h).cast hShape) ((g).cast gShape))) 0).val=0
      · have idle:=blank _ _ occupied
        have cleared : rot (C).queryBits 0 (h.cast hShape) (g.cast gShape) = 0 :=
          congrArg (fun value : ℕ => (value : Cell (C).queryBits))
            (rotor_flat_query_zero_of_inactive u.atlas.board (cfg).rotor (cfg).multiplicity (cfg).grain (cfg).split
              node.val arg.val ((cfg).reg ((payload) (h.cast hShape) (g.cast gShape))) idle)
        exact (congrArg Fin.val cleared).trans_le (by simp)
      · exact (Nat.mod_le ..).trans (((cfg).rotor.flat_query_le_stride u.atlas.board _ _ _ _ _ _).trans
          (Nat.mul_le_mul_left 2 (rotorLimit _ _ occupied)))
    · exact publicLimit _ _
  let q := fun h g=>requestCandidate (requests h g) (bounded h g)
  let rawRead := fun (j : Fin (2*(A).candidates)) (h : Fin (A).hosts) (g : Fin (A).groups) =>(DescentNextSignedWindow.Native.fields (ranked j h g) 0 : Cell (A).signedBits)
  have valid (h : Fin (A).hosts) (g : Fin (A).groups) :
      (kept h g).val + (DescentOperandCandidateLookup.selected q (fun j h g=>((rawRead j h g).val : Cell u.operand.coeff)) h g).val ≤ 2 :=by
    let pick := (q h g).bind (fun j=>ranked j h g)
    have idle (empty_ : issued (h.cast hShape) (g.cast gShape) = 0) : pick=none :=by
      have z : (requests h g).val=0 := congrArg Fin.val empty_
      have absent : q h g = none := by
        unfold q requestCandidate
        rw [dite_eq_left z]
      exact congrArg (fun choice : Option (Fin (2*(A).candidates)) => choice.bind (fun j => ranked j h g)) absent
    have actual := u.issued_ranked_tag (signedBits:=(A).signedBits) (coeff:=u.operand.coeff)
      x₀ arg node values digits name hostEq groupEq X strips signed hubWord tickets
      blank label (h.cast hShape) (g.cast gShape) two pick idle
    cases hit : q h g with
    | none => simpa [DescentOperandCandidateLookup.selected,hit,pick,kept,DescentNextSignedWindow.Native.fields] using actual
    | some j => simpa [DescentOperandCandidateLookup.selected,hit,pick,kept,rawRead] using actual
  exact ⟨⟨q,rawRead,kept,by simpa only [q,requestCandidate_code] using qread,kread,previous,
    fun h g=>(valid h g).trans_lt coeffRoom⟩,valid⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
