import OAI.Hierarchy.DescentNamedResetRootPagesFit
import OAI.Hierarchy.DescentNamedStemNumberFit
import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentResetOriginalNumberRoom
import OAI.Hierarchy.DescentNamedOriginalScalarFit
import OAI.Hierarchy.DescentPhysicalTrunkRoom
import OAI.Hierarchy.DescentResetPublicCuts

namespace OAI
/-! Bounds for each measured original-parent operand on the calendar reset. -/
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

private theorem later_bank {w lo hi : ℕ} {B : Bank} (f : B.Fits w lo) (le : lo≤hi) : B.Fits w hi :=
  ⟨f.1,f.2.1,f.2.2.trans le⟩

/-- The only imported per-stem read is the preceding chronological six-register bank. -/
theorem named_original_number_room
    (lanes : 0<M) (ceiling : (a).fullEnd floor<2^w)
    (markers : ((v).front.donor.markers ((v).front.donorStart early)
      (v).contactShape.shapes (v).contactShape.markerBits).endAddress≤(v).trunkEnd base₀)
    (stem : ∀(x : Fin (ss).blocks) (j : Fin (u).number.stems) t,
      ((u).stemRegisters x.val j.val t).Fits w ((ss).publicFormatEnd r)) :
    (u).numbered.Room r w := by
  let slots:=(v).actor.directory actorBase
  have cuts:=(v).cuts base₀
  obtain ⟨_,_,trunkHigh,massHigh,_,_,_,_⟩ := (a).entered_bounds floor ceiling
  have all : (v).metadataEnd base₀<2^w:=ceiling
  have endFit : (ss).originalEnd r<2^w :=
    (cuts.candidates.trans (cuts.scalar.trans cuts.metadata)).trans_lt all
  obtain ⟨c₀,c₁,c₂,c₃,c₄,c₅⟩:=(ss).number_cuts r
  have deckFit : deck<2^w := (c₁.trans (c₂.trans (c₃.trans (c₄.trans c₅)))).trans_lt endFit
  have markFit : (u).masked.endAddress<2^w := c₀.trans_lt deckFit
  have oldFit : early<2^w := (cuts.trunk.trans ((cuts.mass.trans cuts.joint).trans
    (cuts.privateEnd.trans (cuts.meta.trans c₀)))).trans_lt deckFit
  have relayBegin : early≤(v).privateEnd base₀ :=
    cuts.trunk.trans (cuts.mass.trans (cuts.joint.trans cuts.privateEnd))
  have relayBefore : r≤deck :=by
    have low : r≤(ss).metaEnd r :=(u).masked.mixed.ordered.1.trans (u).masked.mixed.ordered.2
    exact low.trans c₀
  have dir := slots.fits oldFit
  have access : ((v).remap base₀).Fits slots.count slots.inverse w deck := by
    have q:=((v).remap base₀).book_fits slots.count slots.inverse
      (later_bank dir.2.2.2.1 relayBegin) (later_bank dir.2.2.2.2 relayBegin)
      (relayBefore.trans_lt deckFit)
    exact ⟨later_bank q.host relayBefore,later_bank q.low relayBefore,later_bank q.stride relayBefore,
      later_bank q.count relayBefore,later_bank q.inverse relayBefore⟩
  have jobs : (ss).jobs=(ss).blocks*((ss).contacts+(ss).privates):=rfl
  have get (x : Fin (ss).blocks) (j : ℕ) (hj : j<(ss).contacts+(ss).privates) :
      ((u).markRead x.val j).Fits w deck :=by
    apply ProtocolRAMGeneratedWrite.fits_mono _ c₀
    apply (u).measured_mark_fits _ _ _ markFit
    rw [jobs]
    exact (Nat.add_lt_add_left hj _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ x.isLt)
  have f:=(v).original_scalar_fits base₀ N₀ deckFit
  have slotsRoom : (ss).privates≤2^(ss).argBits:=
    (le_max_right 1 (ss).privates).trans (Nat.le_pow_clog (by decide) _)
  apply CandidateSheets.OriginalInputs.of_reads (u).numbered r w
  · let A := (v).contactShape
    have before : A.choicePage ((v).trunkEnd base₀)≤(ss).inputDonorsBase r := by
      have arr:=A.cuts ((v).trunkEnd base₀)
      have toJoint: (v).massEnd base₀≤(v).jointEnd base₀:=cuts.joint
      have earlyScalar:=((v).original_scalar_order base₀).1
      have small:=((v).original_scalar_order base₀).2.1
      exact (arr.2.2.2.2.1.trans arr.2.2.2.2.2).trans (toJoint.trans (earlyScalar.trans small))
    exact A.originalDeckReady _ _ _ scene.donor markers massHigh _ _ before lanes
        (Nat.two_pow_pos _) deckFit
  · intro x j
    refine Fin.cases ?_ (fun t=>?_) j
    · exact ProtocolRAMGeneratedWrite.fits_mono _
        (cuts.mass.trans (cuts.joint.trans (cuts.privateEnd.trans (cuts.meta.trans c₀))))
        ((v).front.trunk_operand_fits early ((v).issuedScene base₀ older) x trunkHigh)
    · exact get x t.val (t.isLt.trans_le (Nat.le_add_right ..))
  · exact fun x=>f.1 x.val
  · exact f.2.2.1
  · exact f.2.2.2
  · exact (ss).originalDonors.label_fits ((ss).inputDonorsBase r) ((v).remap base₀) slots.count slots.inverse
      access deckFit
  · exact (ss).originalDonors.cargo_fits ((ss).inputDonorsBase r) ((v).remap base₀) slots.count slots.inverse
      access deckFit
  · exact stem
  · intro x j
    exact get x ((ss).contacts+j.val) (Nat.add_lt_add_left j.isLt _)
  · exact fun x=>f.1 x.val
  · exact fun _=>f.2.1
  · exact slotsRoom
  · exact endFit

/-- Complete room on the literal named date, including the six chronological stem registers. -/
theorem named_number_room (lanes : 0<M) (ceiling : (a).fullEnd floor<2^w)
    (markers : ((v).front.donor.markers ((v).front.donorStart early)
      (v).contactShape.shapes (v).contactShape.markerBits).endAddress≤(v).trunkEnd base₀) :
    (u).numbered.Room r w :=by
  apply named_original_number_room G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared scene lanes ceiling markers
  intro x j t
  have cuts:=(v).cuts base₀
  have roof : (ss).originalEnd r<2^w := (cuts.candidates.trans (cuts.scalar.trans cuts.metadata)).trans_lt ceiling
  obtain ⟨_,_,bound₁,bound₂,bound₃,bound₄⟩:=(ss).number_cuts r
  apply (u).stem_registers_fit _ ((bound₁.trans (bound₂.trans (bound₃.trans bound₄))).trans_lt roof)
  exact named_root_prepared_end G S board k tail age p f g drift degree payload e previous M nextM
    C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
