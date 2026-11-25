import OAI.Hierarchy.DescentNamedRetainedControlsRead
import OAI.Hierarchy.DescentIssuedCarriedIndex
import OAI.Hierarchy.DescentCarriedOriginFields

namespace OAI
/-! The actual retained serial never exceeds the next date's capacity, even for an unused argument. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentPackedZip
noncomputable section
variable (C : DescentResetOperandSetup.Chart) {U : ℕ} (s : C.Sources) (name : Fin U→Fin C.placement.sparse)
variable (Y : Fin (C.retained.outputs*C.placement.shapes)→Fin C.placement.oldHosts→
    Fin (C.placement.groups*C.placement.blocks)→Cell C.retained.bits)
variable (signals : Fin C.strip→Fin C.placement.oldHosts→Fin (C.placement.groups*C.placement.blocks)→Cell C.signedBits)
variable (x : Fin C.placement.blocks) (arg : Fin C.retained.args) (node : Fin C.retained.nodes)
variable (hub : Fin C.placement.newHosts→Fin C.placement.groups→Cell C.fieldBits)
variable (fee : Fin C.strip→Fin C.placement.newHosts→Fin C.placement.groups→Cell C.fieldBits)
local notation "entry" => C.carriedRow s name Y signals x arg node hub fee

theorem carried_fee_volume (cap : ℕ) (units : 0<C.cable.units) (bound : ∀j h g,(fee j h g).val≤cap)
    (h : Fin C.placement.newHosts) (g : Fin C.placement.groups) : (C.cable.priceField 2 (entry h g)).val≤cap:=by
  apply C.cable.priceField_le_tickets (entry h g) cap units
  intro d j
  let k : Fin C.strip:=finProdFinEquiv (d,j)
  have second : 6+C.strip≤6+C.strip+k.val:=Nat.le_add_right ..
  have value : C.cable.ticket (entry h g) d j=(fee k h g).val:=by
    unfold DescentResetRetainedCableLaw.Shape.ticket DescentResetRetainedCableLaw.Shape.laneIndex DescentResetOperandSetup.Chart.carriedRow
    simp only [ite_true]
    change ((if a:6+C.strip+k.val<4 then _ else if b:6+C.strip+k.val=4 then _ else if c:6+C.strip+k.val=5 then _ else
      if a:6+C.strip+k.val<6+C.strip then _ else _):Cell C.fieldBits).val=_
    simp only [show ¬6+C.strip+k.val<4 by omega,show ¬6+C.strip+k.val=4 by omega,show ¬6+C.strip+k.val=5 by omega,
      Nat.not_lt_of_ge second]
    repeat' erw [dite_false]
    apply congrArg (fun a : Fin C.strip => (fee a h g).val)
    apply Fin.ext
    change (6+C.strip+k.val)-(6+C.strip)=k.val
    omega
  exact value.le.trans (bound k h g)

end
end Hierarchy.DescentResetOperandSetup.Chart

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
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
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "inputAt" pr:arg sc:arg => I₀ previousMeta previousArguments initial pr sc
set_option hygiene false
local notation "u" => inputAt prepared sceneRoom

open DescentResetLocalRoster DescentSixParty.ClosedReset.Window

open DescentResetSourceTicketCompare DescentResetTrunkCompactPointer DescentResetFieldAssembler
open scoped BigOperators

local notation "A₁" => (v).receiver
local notation "F₀" => (v).front
local notation "C₀" => (v).setup
local notation "H₀" => S.hostSize age
local notation "H₁" => S.hostSize (age+1)
local notation "G₁" => S.groupCount (age+1)
local notation "keyWidth" => originalBits D k n (GroupStage.depthBound D n f g)
  input.placement.cap (programCount board (GroupStage.depthBound D n f g)) g
local notation "rank₀" => B.frame.host.symm.toEmbedding.trans (input.vertex.trans (Fin.castLEEmb input.valid.host))
local notation "dense₀" => (B.reset.denseHostRank B.terminals rank₀).trans (Fin.castLEEmb B.next.valid.host)
local notation "rack₀" => rackOf B dense₀
local notation "st" => (v).sheetsStart base₀
local notation "FEE" x:arg j:arg h:arg gr:arg => ∑l,feeAt (wordBefore B) (original_fees (b:=keyWidth) B rack₀ x h gr) j l
local notation "first₀" => (v).operandFloor base₀
local notation "dst" ok:arg m:arg => ((C₀).code first₀ w (u).bank (u).laws).image ((u).beforeSetupImage ok m)

set_option hygiene true

theorem DateInputs.fromNamed_retained_fee_volume
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (paid : input.placement.cap=cap)
    (ok : (u).Ready) (m : Memory w)
    (earned : ActorTrunkReads B input.valid.host (F₀) ((v).actorEnd base₀)
      ((v).issuedScene base₀ (u).earlier) (u).sceneFits m)
    (src : RankSources B (b:=(v).sheets.metaBits) (t:=keyWidth) (M:=(v).sheets.lanes) rack₀
      ((v).rankPorts base₀) (sheetHeader B st (u).sectors.pageBits) (sheetOriginal B st (u).sectors.pageBits)
      (((v).rankPortPhase base₀ w).image ((u).before_ports ok m)))
    :
    ∃(slotAt : Fin (C₀).strip→Fin (totalLocal B))
     (hub : Fin H₁→Fin G₁→Cell (C₀).fieldBits)
     (fee : Fin (2^k)→Fin (C₀).strip→Fin H₁→Fin G₁→Cell (C₀).fieldBits),
      (∀j,(slotAt j).val=2^k*(2*input.placement.cap)+j.val) ∧
      (∀h gr,hub h gr=if ((originalTrunkRack B h).elim .blank (hostShape B)).core then 0 else 1) ∧
      (∀x j h gr,fee x j h gr=(((pointer B.next.valid.host (compactTrunkPeer B input.valid.host) h).elim 0
        (fun h₀=>FEE x (slotAt j) h₀ gr):ℕ):Cell (C₀).fieldBits)) ∧
      (∀x,((v).retainedHub base₀ x).Fits w ((C₀).casts first₀) ∧
        Source ((v).retainedHub base₀ x) hub M (dst ok m)) ∧
      (∀x j,((v).retainedTicket base₀ x j).Fits w ((C₀).casts first₀) ∧
        Source ((v).retainedTicket base₀ x j) (fee x j) M (dst ok m)) ∧
      (∀x j h gr,(fee x j h gr).val≤B.next.placement.cap):=by
  obtain ⟨slotAt,hub,fee,positions,hubs,numbers,seenHub,seenFee⟩:=DateInputs.fromNamed_retained_controls (B:=B)
    drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
    fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom degreeAt paid ok m earned src
  refine ⟨slotAt,hub,fee,positions,hubs,numbers,seenHub,seenFee,?_⟩
  intro x j h gr
  rw [numbers]
  cases dest:pointer B.next.valid.host (compactTrunkPeer B input.valid.host) h with
  | none=>simp
  | some target=>
    simp only [Option.elim_some]
    exact (Nat.mod_le ..).trans (sum_fee_le (b:=keyWidth) B rack₀ x target gr (slotAt j))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
