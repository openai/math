import OAI.Hierarchy.DescentNamedPanelPublicCapacity
import OAI.Hierarchy.DescentDateTaggedOrdinals
import OAI.Hierarchy.DescentNamedReachedCandidates

namespace OAI
/-! # Operand cells of the ranked reset after the original private and public publishers -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
set_option maxRecDepth 6144
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
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
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
local notation:max "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation:max "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
local notation:max "deck" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (liveAt x) (regsAt x)

local notation "cfg" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation:max "operandValues" x:arg menu:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (liveAt x) (regsAt x) menu rfl ((x):Fin (v).receiver.blocks).val
local notation "panels" => DateInputs.OperandPanelsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
  venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom

/-- The two public facts needed by the retained field join, on the native public operand bank. -/

local notation "G₁" => S.groupCount (age+1)
local notation "r" => (C₀).retained
local notation "issuedFields" => DateInputs.IssuedFieldsAt G S board k tail age p f g drift degree payload e previous
  M nextM C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut
  count previousMeta previousArguments initial prepared sceneRoom
local notation "Ksig" => Fin (C₀).strip→Fin (C₀).placement.oldHosts→Fin ((C₀).placement.groups*(C₀).placement.blocks)→Cell (C₀).signedBits
local notation "pHost" => Fin (C₀).placement.newHosts
local notation "pGroup" => Fin (C₀).placement.groups
local notation:max "rawName" size:arg j:arg => ((Z).rawAtIndex T rank j).cast size

local notation:max "fetch" gg:arg hx:arg hj:arg peers:arg h:arg gr:arg x:arg j:arg =>
  ((physicalRack (((h):Fin (A₁).hosts).cast peers)).bind (fun z=>
    candidateRows B (fieldNames B) ((((gr):Fin (A₁).groups).cast gg,z),((x):Fin (A₁).blocks).cast hx)
      (((j):Fin (2*(A₁).candidates)).cast (congrArg (2*·) hj))))

/-- All original selected fields may be read on any row the genuine public publishers produced. -/
def DateInputs.FreshInputsAt (ready : (u).Ready) (actors : Memory w) : Prop :=
  ∃(hx : (A₁).blocks=2^k) (hj : (A₁).candidates=totalLocal B) (groupsAt : (A₁).groups=G₁)
    (aligned : (A₁).hosts=(v).sheets.hosts) (geo : (C₀).MovementShape)
    (size : HH*rows=(C₀).placement.sparse) (X₁ : (C₀).seven.Packets) (strips : (r).Strips) (sig : Ksig)
    (marks : pHost→pGroup→Cell (C₀).fieldBits)
    (fees : Fin (C₀).placement.blocks→Fin (C₀).strip→pHost→pGroup→Cell (C₀).fieldBits),
    (∀i j,let y:=(v).operandIndex (u).operand i
      Source ((v).previous (u).operand draw base₀ i j)
        (fun h gr=>ResetOutput.signedCandidateField (A₁).signedBits y.2.1
          (fetch groupsAt hx hj aligned h gr (y.1) j)) (A₁).lanes ((u).operandEntry ready actors)) ∧
    ∀(block : Fin (A₁).blocks) (arg : Fin (r).args) (node : Fin (r).nodes)
      (values : (deck block).Values (C₀).placement.newHosts (C₀).placement.groups),
      (u).PublicValuesRead ready actors (block.cast (u).operandBlocks) rfl (fun j:Fin (Fintype.card B.next.V)=>rawName size j) values →
      issuedFields ready actors block arg node values (fun j:Fin (Fintype.card B.next.V)=>rawName size j)
        geo.host geo.groups X₁ strips sig marks (fees (block.cast (u).operandBlocks))

theorem DateInputs.fresh_inputs_from_panels (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (ready : (u).Ready) (m : Memory w) (archived : (r).Values)
    (held : panels degreeAt capAt ready m archived) :
    ∃actors:Memory w,(u).ThroughActors ((entry₀).image m) actors ∧
      (u).throughOperandDate.Runs ((entry₀).image m) ((u).sheetsResult ready actors) ∧
      DateInputs.FreshInputsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
        venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom ready actors:=by
  obtain ⟨μ,measured,after,_,_,_,scan,publish,requests,_,_,_,_,completed,hx,hj,groupsAt,_,aligned,source⟩:=held
  obtain ⟨_,_,X₁,signals,geo,dim,size,marks,fees,_,_,_,_,_,issued⟩:=requests
  exact ⟨after,(DateInputs.classified_prefix («u» := (u)) ready scan publish).1,completed,
    hx,hj,groupsAt,aligned,geo,size,X₁,_,signals,marks,fees,source,issued⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
