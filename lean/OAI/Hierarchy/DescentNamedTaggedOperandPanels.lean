import OAI.Hierarchy.DescentNamedPanelPublicCapacity
import OAI.Hierarchy.DescentNamedTaggedOperandRows
import OAI.Hierarchy.DescentDateTaggedOrdinals

namespace OAI
/-! The packed reset tags and their reads on the one attained post-actor memory. -/
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
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
  (sceneRoom : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "HH" => S.hostSize age

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
open DescentSharedCableNames
local notation "A₁" => (v).receiver
local notation "ST" => (v).sheetsStart base₀
local notation "plan" => (v).linkedRankInputs (u).sectors ST
local notation "draw" => (v).renderFromRanks plan base₀
local notation "physicalRack" => rackOf B (((Z).denseHostRank T rank).trans (Fin.castLEEmb B.next.valid.host))
open DescentResetTrunks
local notation "C₀" => (v).setup

local notation "ctrl" => (v).controlRegisters
local notation "controlStart" => (v).controlFloor base₀
local notation "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
local notation "deck" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (liveAt x) (regsAt x)

local notation "cfg" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation "operandValues" x:arg menu:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (liveAt x) (regsAt x) menu rfl ((x):Fin (v).receiver.blocks).val
local notation "sm" => (ResetOutput.named_ticket_limits G S board k tail age p f g drift degree payload e previous M
  nextM C packet prior_ base₀).1
local notation "panels" => DateInputs.OperandPanelsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom

local notation "pubRows" => DateInputs.PublicOperandRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom

/-- The source and destination of the returned receipt are the actual reached actor state. -/
theorem DateInputs.tagged_from_operand_panels (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (ready : (u).Ready) (m : Memory w) (archived : (C₀).retained.Values)
    (held : panels degreeAt capAt ready m archived) :
    ∃after : Memory w, (u).ThroughActors ((entry₀).image m) after ∧
      (u).throughOperandDate.Runs ((entry₀).image m) ((u).sheetsResult ready after) ∧
      (pubRows ready after → (u).TaggedOrdinals ready sm after):=by
  obtain ⟨μ,measured,after,_,_,_,scan,publish,requests,_,_,_,_,completed,
    hx,hj,gg,_,aligned,source⟩:=held
  have acted : (u).ThroughActors ((entry₀).image m) after:=
    (DateInputs.classified_prefix («u»:=u) ready scan publish).1
  refine ⟨after,acted,completed,?_⟩
  intro menus arg block node
  obtain ⟨_,_,X₀,signals,geo,dim,size,hubWord,fees,_,moved,_,_,controls,_⟩:=requests
  obtain ⟨_,_,marked,dated,cash⟩:=controls
  obtain ⟨menu,valid,capWord⟩:=menus size block
  let people:=fun j h gr => (physicalRack ((h:Fin (A₁).hosts).cast aligned)).bind (fun site=>
    candidateRows B (fieldNames B) (((gr:Fin (A₁).groups).cast gg,site),block.cast hx)
      ((j:Fin (2*(A₁).candidates)).cast (congrArg (2*·) hj)))
  let arr:=fun (f₀ : Fin 7) j h gr =>(ResetOutput.pointerField f₀).elim (0:Cell (A₁).signedBits)
    (fun field=>(DescentNextSignedWindow.Native.fields (people j h gr) field:ℕ))
  let id:=fun f₀=>(v).operandOrdinal (u).operand f₀ arg block node
  have get (f₀ : Fin 7) (j : Fin (2*(A₁).candidates)) :
      Source ((v).previous (u).operand draw base₀ (id f₀) j) (arr f₀ j) (A₁).lanes ((u).operandEntry ready after):=by
    simpa only [id,ResetOutput.operandIndex_ordinal,arr,people] using source (id f₀) j
  have shared j h gr:((arr 2 j h gr).val:Cell (u).operand.coeff).val≤B.next.placement.cap:=
    (Nat.mod_le ..).trans ((Nat.mod_le ..).trans
        (candidate_shared_le B (fieldNames B) (physicalRack (h.cast aligned)) (gr.cast gg) (block.cast hx)
          (j.cast (congrArg (2*·) hj))))
  have tag (j : Fin (2*(A₁).candidates)) :
      Source ((v).previous (u).operand draw base₀ (id 0) j)
        (fun h gr=>(DescentNextSignedWindow.Native.fields (people j h gr) 0 : Cell (A₁).signedBits))
        (A₁).lanes ((u).operandEntry ready after):=get 0 j
  exact DateInputs.fromNamed_tagged_rows B drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    ready after block arg node menu _ geo.host geo.groups X₀ _ signals hubWord (fees (block.cast (u).operandBlocks))
    capAt moved (marked _) (dated _) valid capWord (cash _) arr get shared people tag

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
