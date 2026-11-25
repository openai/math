import OAI.Hierarchy.DescentDatedIssuedRoles
import OAI.Hierarchy.DescentIssuedOrdinalRoom
import OAI.Hierarchy.DescentIssuedQueryBudget

namespace OAI
/-! Reconstruct all seven native ordinal fields from the actual retained, rotor and public tickets. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSIMDLookup DescentResetOperandSetup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
/-- A cleared activity register suppresses the rotor request. -/
theorem rotor_flat_query_zero_of_inactive {n h : ℕ} (graph : NonlinearExpanders.Graph n h)
    (shape : DescentRotorOperandQueryROM.Shape) (mult grain split node arg : ℕ)
    (table : Fin 4 → Cell shape.fieldBits) (zero : (table 1).val = 0) :
    shape.flatReg graph mult grain split node arg 0 table = 0 := by
  unfold DescentRotorOperandQueryROM.Shape.flatReg
  split
  next nonempty => exact (Nat.ne_of_gt nonempty.1 zero).elim
  next => rfl

private theorem clip_dyadic (x bits coeff : ℕ) :
    (((x : Cell coeff) % 2^bits).val) = ((x % 2^bits : ℕ) : Cell coeff).val := by
  have castPower : (2^bits : Cell coeff) = ((2^bits : ℕ) : Cell coeff) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [castPower, Fin.val_mod, Fin.val_natCast, Fin.val_natCast, Fin.val_natCast]
  rcases le_total bits coeff with smaller | larger
  · exact (Nat.mod_mod_eq_mod_mod_mod_of_dvd (Nat.pow_dvd_pow 2 smaller)).symm
  · have divides := Nat.pow_dvd_pow 2 larger
    rw [Nat.mod_eq_zero_of_dvd divides, Nat.mod_zero, Nat.mod_mod_of_dvd _ divides]

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

include lanes in
set_option maxHeartbeats 2200000 in
def ordinal_from_tickets (width : (C).queryBits=(v).receiver.queryBits) (pitch : (C).lanes=(v).receiver.lanes) (moved : (C).Moved base (s) name (((C).sources base w (s)).image m) (Ys) signed)
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
    (cable : ∀(h : Fin (A).hosts) (g : Fin (A).groups) (j : Fin (2*(A).candidates)), f=2→(carried ((h).cast hShape) ((g).cast gShape)).val=j.val+1→
      0<((oldCell f ((h).cast hShape) ((g).cast gShape)).val+(surcharge f ((h).cast hShape) ((g).cast gShape)).val : ℕ)%(2^(C).fieldBits) →
      0<(addend rawSigned j h g) → (((oldCell f ((h).cast hShape) ((g).cast gShape)).val+
        (surcharge f ((h).cast hShape) ((g).cast gShape)).val:ℕ)%(2^(C).fieldBits):Cell u.operand.coeff).val+addend rawSigned j h g<2^u.operand.coeff)
    (rotor : ∀(h : Fin (A).hosts) (g : Fin (A).groups) (j : Fin (2*(A).candidates)), f=2→(rot (C).queryBits 0 ((h).cast hShape) ((g).cast gShape)).val=j.val+1→
      0<(rot (C).fieldBits f.succ ((h).cast hShape) ((g).cast gShape)).val→0<(addend rawSigned j h g)→
      ((rot (C).fieldBits f.succ ((h).cast hShape) ((g).cast gShape)).val:Cell u.operand.coeff).val+addend rawSigned j h g<2^u.operand.coeff)
    (surface : ∀(h : Fin (A).hosts) (g : Fin (A).groups) (j : Fin (2*(A).candidates)), f=2→(pub (C).queryBits none ((h).cast hShape) ((g).cast gShape)).val=j.val+1→
      0<(pub (C).fieldBits (some f) ((h).cast hShape) ((g).cast gShape)).val→0<(addend rawSigned j h g)→
      ((pub (C).fieldBits (some f) ((h).cast hShape) ((g).cast gShape)).val:Cell u.operand.coeff).val+addend rawSigned j h g<2^u.operand.coeff) :
    OrdinalRead u ok small actorMem (ord f) :=by
  let requests (h : Fin (A).hosts) (g : Fin (A).groups) := (issued ((h).cast hShape) ((g).cast gShape)).cast (congrArg (2^·) width)
  let kept (h : Fin (A).hosts) (g : Fin (A).groups) := ((stored f ((h).cast hShape) ((g).cast gShape)).val:Cell u.operand.coeff)
  have actual:=u.issued_ordinal ok actorMem x₀ arg node values digits lanes name hostEq groupEq X strips
    signed hubWord tickets width pitch moved marked dated rawFit aux coords packet live regs blank label two f
  have qread : Source (u.operand.query (ord f)) requests (A).lanes (u.operandEntry ok actorMem):=
    cast_grid hShape gShape (u.operand.query (ord f)) (fun h g => (issued h g).cast (congrArg (2^·) width))
      (A).lanes (u.operandEntry ok actorMem) actual.1
  have kread : Source (u.operand.kept (ord f)) kept (A).lanes (u.operandEntry ok actorMem):=
    cast_grid hShape gShape (u.operand.kept (ord f)) (fun h g => ((stored f h g).val : Cell u.operand.coeff))
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
  refine OrdinalRead.ofIssued u f arg x₀ node ok actorMem small requests kept qread kread bounded rawSigned previous ?_
  intro ptr h g j code positive nonzero
  change (issued ((h).cast hShape) ((g).cast gShape)).val=j.val+1 at code
  change 0<((stored f ((h).cast hShape) ((g).cast gShape)).val:Cell u.operand.coeff).val at positive
  change ((stored f ((h).cast hShape) ((g).cast gShape)).val:Cell u.operand.coeff).val+addend rawSigned j h g<_
  have serial : f=2:=by
    by_contra different
    have notTwo : f.val≠2:=fun e=>different (Fin.ext (by simpa using e))
    have early : f.val < 2 := lt_of_le_of_ne (Nat.le_of_lt_succ ptr) notTwo
    have nonzeroQuery : issued ((h).cast hShape) ((g).cast gShape)≠0:=by
      intro empty_
      rw [empty_] at code
      simp at code
    have zeroField:=u.issued_head_zero x₀ arg node values digits name hostEq groupEq X strips
      signed hubWord tickets blank label f ((h).cast hShape) ((g).cast gShape) two early nonzeroQuery
    have castZero : ((stored f (h.cast hShape) (g.cast gShape)).val : Cell u.operand.coeff) = 0 :=
      congrArg (fun value : Cell (C).fieldBits => (value.val : Cell u.operand.coeff)) zeroField
    exact (Nat.ne_of_gt positive) ((congrArg Fin.val castZero).trans (by simp))
  have owner:=u.issued_role_at x₀ arg node values digits name hostEq groupEq X strips signed hubWord tickets
    blank label f ((h).cast hShape) ((g).cast gShape)
  rcases owner with ⟨qeq,field⟩|⟨qeq,field⟩|⟨qeq,field⟩
  · rw [qeq] at code
    rw [field] at positive ⊢
    have paid := cable h g j serial code (lt_of_lt_of_le positive (Nat.mod_le ..)) nonzero
    simpa only [clip_dyadic, Fin.val_natCast] using paid
  · rw [qeq] at code
    rw [field] at positive ⊢
    exact rotor h g j serial code (lt_of_lt_of_le positive (Nat.mod_le ..)) nonzero
  · rw [qeq] at code
    rw [field] at positive ⊢
    exact surface h g j serial code (lt_of_lt_of_le positive (Nat.mod_le ..)) nonzero
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
