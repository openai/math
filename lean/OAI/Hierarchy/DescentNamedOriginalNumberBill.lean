import OAI.Hierarchy.DescentNamedOriginalNumberRoom
import OAI.Hierarchy.DescentOriginalNumberInvoice

namespace OAI
/-! Literal original-number CPU invoice under the actual emitted, signed operand selection. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : Dated.Operands) (floor w : ℕ)
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
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
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
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor (namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
    (scene : ((((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared scene
local notation "ss" => (v).sheets
local notation "r" => ((v).remap base₀).endAddress
local notation "deck" => (ss).inputDonorsEnd r
local notation "N₀" => 2^k*(2*cap)


open DescentStaticWordColumn

local notation "U₀" => (256+28*((v).front.signedQueries/2))
local notation "V₀" => (v).contactShape.originalWork

theorem named_original_work : (u).numbered.Inputs r U₀ V₀ 64 := by
  let A:=(v).contactShape
  let F:=(v).trunkEnd base₀
  let D:=(v).front.donorStart early
  let src:=(v).issuedScene base₀ older
  have seen:=A.originalSensorsAt_work D F src.donor (ss).originalDonors.slots
  have z (x : ℕ) : ((v).originalZero base₀ x).work≤7 := by
    unfold ResetOutput.originalZero DescentResetOriginalZeroHalo.zero
    split
    · change 7 ≤ 7
      exact le_rfl
    · change 1 ≤ 7
      decide
  have fieldWork (j : Fin 3) (src : Bank) :
      (DescentResetOriginalZeroHalo.field ((v).originalWordsBase base₀) (ss).hosts (ss).groups (ss).lanes
        (ss).metaBits j src).work≤64:=by
    change 25 ≤ 64
    decide
  let R:=(v).remap base₀
  let dir:=(v).actor.directory actorBase
  have loader (raw : Bank) : (R.load dir.count dir.inverse (.lookup raw .row)).work≤201 :=by
    exact R.load_work dir.count dir.inverse (.lookup raw .row)
  refine ⟨?_,?_,?_,?_,?_,?_,seen.1,seen.2.1,seen.2.2,?_,?_,?_,?_,?_⟩
  · intro x j
    refine Fin.cases ?_ (fun t=>?_) j
    · exact ((v).front.trunk_operand_work early x.val).trans (by omega)
    · change 7≤U₀
      omega
  · intro x;exact (z x.val).trans (by omega)
  · intro x;exact (fieldWork 0 ((v).originalAux base₀ 0)).trans (by omega)
  · intro x;exact (fieldWork 1 ((v).originalAux base₀ 1)).trans (by omega)
  · intro x f j;exact (loader _).trans (by omega)
  · intro x f t j;exact (loader _).trans (by omega)
  · intro x j t;exact (u).stem_registers_work x.val j.val t
  · intro x; change 7 ≤ 64; decide
  · intro i;exact (z _).trans (by decide)
  · intro i; change 25 ≤ 64; decide
  · intro i; change 25 ≤ 64; decide

theorem named_original_invoice (lanes : 0<M) (ceiling : (a).fullEnd floor<2^w)
    (markers : ((v).front.donor.markers ((v).front.donorStart early)
      (v).contactShape.shapes (v).contactShape.markerBits).endAddress≤(v).trunkEnd base₀) :
    (u).numbered.time r+7*names ((u).numbered.code r w)≤(u).numbered.invoice r U₀ V₀ 64 :=by
  apply CandidateSheets.OriginalInputs.literal_invoice
  · exact named_number_room G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
      previousMeta previousArguments initial prepared scene lanes ceiling markers
  · exact named_original_work G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
      previousMeta previousArguments initial prepared scene

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
