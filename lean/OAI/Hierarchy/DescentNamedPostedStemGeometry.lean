import OAI.Hierarchy.DescentDateStemRegisterRead
import OAI.Hierarchy.DescentOriginalBoardGeometry
import OAI.Hierarchy.DescentNamedScalarLayout

namespace OAI
/-! # Register dimensions of the scheduled stem passes -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentResetLocalRoster DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCommonHost DescentFallbackPeriod DescentRecordedRotorLayers DescentSIMDLookup
open DescentDenseHostOrder DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)

variable (date : PhysicalReset)
local notation "v" => date.successor
local notation "sh" => (v).sheets

/-- The public widths and index bounds used by the six stem register reads. -/
structure PostedStemGeometry : Prop where
  schedule : (sh).stemSources=numberPlan B (sh).hosts (sh).lanes (sh).stemBits
    (sh).stemSignedBits (sh).metaBits (sh).metaBits
  xRoom : 2^k≤(v).front.blocks
  jRoom : stemsCount B≤(v).front.signedQueries
  cap : date.c/2=input.placement.cap
  signedWidth : DescentSignedCableCodec.width input.placement.degree input.placement.cap≤(sh).stemSignedBits
  metaPos : 0<(sh).metaBits
  signedFits : DescentSignedCableCodec.width input.placement.degree input.placement.cap≤(sh).stemBits
  groupsFit : 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)<2^(sh).stemBits
  hostsFit : 2*(input.placement.degree+1)+1<2^(sh).stemBits
  fineFit : k≤(sh).stemBits

variable (p drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
    (venue : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "a" => named G S ctl.board k tail i p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "paidCap" => ((capCalendar G.b S.rounds g S.height).take i).prod*256

theorem named_posted_stem_geometry (paid : input.placement.cap=paidCap) (priorDegree : venue.degree=D) :
    PostedStemGeometry B (a) := by
  subst D
  let ht:=GroupStage.depthBound venue.degree n f g
  let shapes:=(DescentDenseHostOrder.roster ctl.board k ht).card
  have widths:=CandidateSheets.stem_width S ctl.board k tail i venue.degree f g paidCap M
  refine ⟨scheduled_stem_plan B ctl.board paidCap M,le_rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change stemsCount B≤2*(2^k*(2*paidCap))
    exact (congrArg (2*·) (original_donor_domain B paid)).symm.le
  · change (2*paidCap)/2=input.placement.cap
    rw [paid]
    omega
  · rw [input.branch,paid]
    change DescentSignedCableCodec.width venue.degree paidCap≤ResetMiddle.fieldWidth venue.degree paidCap n k ht
    exact ((Nat.le_max_left ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_left ..)
  · change 0<CandidateFront.endpointWidth venue.degree shapes (2^g*paidCap)
    apply lt_of_lt_of_le _ (le_max_left ..)
    have pos : 1 < Nat.max 5 (2^g*paidCap+2) := (by decide : 1 < 5).trans_le (Nat.le_max_left _ _)
    have big:Nat.max 5 (2^g*paidCap+2)≤2^Nat.clog 2 (Nat.max 5 (2^g*paidCap+2)):=Nat.le_pow_clog (by decide) _
    change 0<Nat.clog 2 _
    by_contra! no
    simp only [Nat.le_zero.mp no,pow_zero] at big
    omega
  · rw [input.branch,paid]
    exact widths.1
  · rw [B.commonDepth,Nat.add_sub_cancel_left]
    exact widths.2.1
  · rw [input.branch]
    exact widths.2.2
  · change k≤ max (DescentSignedCableCodec.width venue.degree paidCap)
      (max (k+1) (Nat.clog 2 (2*(venue.degree+1)+2)))
    exact (Nat.le_succ k).trans ((Nat.le_max_left ..).trans (Nat.le_max_right ..))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
