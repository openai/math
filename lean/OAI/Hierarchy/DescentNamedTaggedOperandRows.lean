import OAI.Hierarchy.DescentNamedIssuedOrdinal
import OAI.Hierarchy.DescentDatedTaggedOrdinalRows
import OAI.Hierarchy.DescentNamedTicketGeometry
import OAI.Hierarchy.DescentNamedRetainedFeeVolume

namespace OAI
/-! The signed reset output from a single physical argument date, using the actual cap and original ballot formats. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
private theorem emptyRotorField {n d : ℕ} (graph : NonlinearExpanders.Graph n d)
    (shape : DescentRotorOperandQueryROM.Shape) (mult grain split node arg : ℕ) (field : Fin 8)
    (table : Fin 4 → Cell shape.fieldBits) (idle : (table 1).val=0) :
    shape.flatReg graph mult grain split node arg field table=0 := by
  unfold DescentRotorOperandQueryROM.Shape.flatReg
  split
  next active => exact (Nat.ne_of_gt active.1 idle).elim
  next => rfl

private theorem ticketRoomsOfStage (a : PhysicalReset) (stage : ResetOutput) (same : a.successor=stage)
    (room : 2*stage.receiver.candidates<2^stage.receiver.queryBits ∧
      1+2*stage.setup.cable.strip≤2*stage.receiver.candidates) :
    2*a.successor.receiver.candidates<2^a.successor.receiver.queryBits ∧
      1+2*a.successor.setup.cable.strip≤2*a.successor.receiver.candidates := by
  rw [same]
  exact room

variable {F AP : Type} [Field F] {d : ℕ} {abits : AP→ℕ} {W : MarkedWorld F d AP abits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
    {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
    (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "inputAt" pr:arg sc:arg => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
  initial pr sc

local notation "pri" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "givenRooms" => ResetOutput.named_ticket_limits G S board k tail age p f g drift degree payload e previous M nextM
  C packet pri base₀
local notation "stageRooms" => ticketRoomsOfStage (a) _
  (named_successor G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor)
  ⟨(givenRooms).1,(givenRooms).2.1⟩
local notation "small" => (stageRooms).1

set_option hygiene false
local notation "I" => inputAt prepared scene

open DescentPackedZip DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
local notation "hw" => (v).setup
local notation "r₀" => (hw).retained
local notation "hh" => (hw).placement.newHosts
local notation "gg" => (hw).placement.groups
local notation "base" => (v).operandFloor base₀
local notation "m" => (I).beforeSetupImage ok actorMem
local notation "cfg" => publicOperands (I).atlas (I).roots (I).menu.payload
local notation "x" => x₀.cast (I).operandBlocks
local notation "ctrl" => (v).controlRegisters
local notation "controls" => (v).controlFloor base₀
local notation "actor" => (v).actor
local notation "origin" => (v).middle.stop base₀
local notation "active" => (ctrl).live controls (x).val
local notation "reg" => (ctrl).ports controls ((a).c/2) (x).val ((actor).directory origin).inverse
    ((actor).depths origin) ((actor).levels origin)
local notation "ports" => OperandMenu.publicPorts («a» := (a)) (I).shape start (I).count (I).hub (I).g (I).Y active reg
local notation "s" => (I).bank
local notation "Ys" => (hw).assignedDigits hostEq groupEq (s).which X strips
local notation "raw" => (hw).carriedRow (s) name (Ys) signed x arg node hubWord tickets
local notation "rowData" => (I).menu.publicData (I).shape start (I).count (I).hub (I).g (I).Y active reg values rfl (x).val
local notation "at_" => (finProdFinEquiv (arg,node) : Fin (hw).members)
local notation "dst" => ((hw).code base w (s) (I).laws).image m
local notation "oldCell" f:arg h:arg k:arg => ((DescentRetainedTargetPlacement.Chart.compact (hw).placement (hw).seven.batch
  (s).primary name (Ys) ((r₀).outputID 1 f arg node) x h k).val : Cell (hw).fieldBits)
local notation "rot" width:arg f:arg h:arg k:arg => ((cfg).rotor.flatReg (I).atlas.board (cfg).multiplicity (cfg).grain (cfg).split
   node.val arg.val f ((cfg).reg ((rowData) h k)) : Cell width)
local notation "pub" width:arg f:arg h:arg k:arg => (cfg).column (I).atlas.board width f at_ ((rowData) h k)
local notation "mark" => (v).retainedHub base₀ x
local notation "fee" => (v).retainedTicket base₀ x
local notation "ord" f:arg => (v).operandOrdinal (I).operand f arg x₀ node

open DescentSixParty.Chronology.DatePorts DescentOperandWidth DescentResetLocalRoster
local notation "A" => (v).receiver
local notation "draw" => (v).renderFromRanks ((v).linkedRankInputs (I).sectors ((v).sheetsStart base₀)) base₀
local notation "maxVol" => max (publicCap S) (2^k*(2*input.placement.cap))
set_option hygiene true

set_option maxHeartbeats 1400000 in
theorem DateInputs.fromNamed_tagged_rows
    (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (ok : (I).Ready) (actorMem : Memory w) {N : ℕ}
    (x₀ : Fin (v).receiver.blocks) (arg : Fin (r₀).args) (node : Fin (r₀).nodes)
    (values : (ports).Values hh gg)
    (name : Fin N→Fin (hw).placement.sparse)
    (hostEq : (hw).placement.oldHosts=(r₀).hosts) (groupEq : (hw).placement.groups*(hw).placement.blocks=(r₀).grouped)
    (X : (hw).seven.Packets) (strips : (r₀).Strips)
    (signed : Fin (hw).strip→Fin (hw).placement.oldHosts→Fin ((hw).placement.groups*(hw).placement.blocks)→Cell (hw).signedBits)
    (hubWord : Fin hh→Fin gg→Cell (hw).fieldBits) (tickets : Fin (hw).strip→Fin hh→Fin gg→Cell (hw).fieldBits)
    (capAt : input.placement.cap=cap)
    (moved : (hw).Moved base (s) name (((hw).sources base w (s)).image m) (Ys) signed)
    (marked : (mark).Fits w ((hw).casts base) ∧ Source mark hubWord (hw).lanes dst)
    (dated : ∀j,(fee j).Fits w ((hw).casts base) ∧ Source (fee j) (tickets j) (hw).lanes dst)
    (publicRead : (I).PublicValuesRead ok actorMem x rfl name values)
    (capacity : ∀h g,((cfg).oldConfig.header ((cfg).basic ((rowData) h g)) 0).val≠0 →
        ((cfg).reg ((rowData) h g) 0).val=input.placement.cap)
    (cash : ∀j h gr,(tickets j h gr).val≤B.next.placement.cap)
    (rawSigned : Fin 7→Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
    (prev : ∀f j,Source ((v).previous (I).operand draw base₀ (ord f) j) (rawSigned f j) (A).lanes ((I).operandEntry ok actorMem))
    (rankedCap : ∀j h g,((rawSigned 2 j h g).val:Cell (I).operand.coeff).val≤B.next.placement.cap)
    (ranked : Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Option
      (DescentNextSignedWindow.Record B.next.placement.degree B.next.placement.cap))
    (tagSource : ∀j,Source ((v).previous (I).operand draw base₀ (ord 0) j)
      (fun h g=>(DescentNextSignedWindow.Native.fields (ranked j h g) 0:Cell (A).signedBits))
      (A).lanes ((I).operandEntry ok actorMem)) :
    (∀f,Nonempty (OrdinalRead (I) ok small actorMem (ord f))) ∧
    ∃r : OrdinalRead (I) ok small actorMem (ord 0),∀h g,
      (r.kept h g).val+(DescentOperandCandidateLookup.selected r.query
        (fun j h g=>((r.raw j h g).val:Cell (I).operand.coeff)) h g).val≤2:=by
  have rawFit:=DateInputs.named_raw_operand_access G S board k tail age p f g drift degree payload e previous M
    nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared scene ok.full ok.placed
  have bound : 2≤(hw).fieldBits:=by
    change 2≤ max (max (max 2 _) _) _
    exact ((Nat.le_max_left ..).trans (Nat.le_max_left ..)).trans (Nat.le_max_left ..)
  have two : 2<2^(hw).fieldBits:=by
    exact (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) bound)

  have nextCap:B.next.placement.cap≤publicCap S :=
    B.next.valid.capacity.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left _ B.age) _))
  have units : 0<(hw).cable.units:=by
    change 0<ResetInput.calendarLanes S G.b (age+1)
    dsimp [ResetInput.calendarLanes,DescentCompiler.AtomSchedule.grainAt]
    have positive:=G.base_pos
    positivity
  have half : (a).c/2=cap:=by
    change (2*cap)/2=cap
    omega
  obtain ⟨aux,coord,packetRead,onRead,register,blank,label⟩:=publicRead
  have reserve (rh : Fin hh) (rg : Fin gg)
      (hit : ((cfg).oldConfig.header ((cfg).basic ((rowData) rh rg)) 0).val≠0) :
      ((cfg).reg ((rowData) rh rg) 0).val=cap := (capacity rh rg hit).trans capAt
  let decoder := DateInputs.issued_tagged_rows («a»:=(a)) (floor:=start) (w:=w) (U:=N) (I)
    ok actorMem x₀ arg node values rfl rfl name hostEq groupEq X strips signed hubWord tickets
  let observed := decoder rfl rfl moved marked dated rawFit aux coord packetRead onRead register blank label two
  let bounded := observed small rfl rfl rawSigned prev (deg:=B.next.placement.degree)
    (target:=B.next.placement.cap) ranked tagSource (stageRooms).2
  apply bounded (volume:=maxVol)
  · intro rh rg hit
    rw [DescentRotorOrientedQuery.stride_eq_publicSlots,reserve rh rg hit]
    exact le_rfl
  · intro rh rg _ _
    have issued : (pub (hw).queryBits none rh rg).val≤2*publicSlots board Ht k ((a).c/2):=
      DescentResetOperandSetup.Chart.public_query_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ((rowData) rh rg) at_ (fun hit=>(reserve rh rg hit).trans half.symm)
    change (pub (hw).queryBits none rh rg).val≤2*publicSlots board Ht k cap
    calc
      _ ≤ 2*publicSlots board Ht k ((a).c/2):=issued
      _ = _ :=congrArg (fun t=>2*publicSlots board Ht k t) half
  · exact ClosedReset.Window.serial_roster_space B tail drift degree p
  · exact (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide)
      (show 2≤(I).operand.coeff from
        (DescentOperandWidth.wide G S k tail drift degree).trans (Nat.le_max_left ..)))
  · exact fun j rh rg=>(rankedCap j rh rg).trans (nextCap.trans (Nat.le_max_left ..))
  · exact fun rh rg=>((hw).carried_fee_volume (s) name (Ys) signed x arg node hubWord tickets B.next.placement.cap
      units cash rh rg).trans (nextCap.trans (Nat.le_max_left ..))
  · intro rh rg
    by_cases empty_ : ((cfg).oldConfig.header ((cfg).basic ((rowData) rh rg)) 0).val=0
    · have idle:=blank rh rg empty_
      have cleared := emptyRotorField (I).atlas.board (cfg).rotor (cfg).multiplicity (cfg).grain (cfg).split
        node.val arg.val (2:Fin 7).succ ((cfg).reg ((rowData) rh rg)) idle
      exact (Nat.mod_le ..).trans (cleared.le.trans (Nat.zero_le _))
    · have prior:=capacity rh rg empty_
      have bitrate : ctl.bitsR≤2^f:=(Nat.le_mul_of_pos_left _ (pow_pos (Nat.two_pow_pos n) 2)).trans ctl.rows
      have bounded : ((cfg).reg ((rowData) rh rg) 0).val≤2^(8+S.capGain*age):=prior.symm ▸ input.valid.capacity
      have charge := (cfg).rotor.flat_serial_reserve board C (cfg).grain (cfg).split node.val arg.val
        (2^(8+S.capGain*age)) ((cfg).reg ((rowData) rh rg)) rfl (Nat.two_pow_pos _) bounded bitrate
      apply (Nat.mod_le ..).trans (charge.trans ?_)
      apply le_trans _ (Nat.le_max_left ..)
      change 2^(reserveGain h C f)*2^(8+S.capGain*age)≤2^(8+S.capGain*S.length)
      rw [←ctl.gain,←pow_add]
      apply Nat.pow_le_pow_right (by decide)
      have after_:=Nat.mul_le_mul_left S.capGain B.age
      rw [Nat.mul_succ] at after_
      have step:=ctl.cap
      omega
  · change 2^k*(2*((a).c/2))≤_
    rw [half,←capAt]
    exact Nat.le_max_right ..

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
