import OAI.Hierarchy.DescentNamedResetAtlas
import OAI.Hierarchy.DescentResetAtlasRoom
import OAI.Hierarchy.DescentResetMiddleCalendar
import OAI.Hierarchy.DescentResetReceiverPitch
import OAI.Hierarchy.DescentPhysicalResetBooks

namespace OAI
/-! Word bounds and the final address of the literal root tables on the dated reset. -/
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
variable (fitsStencil : e ≤ laneBits (S.groupWidth k tail age + k) payload
    (S.localWalshBits p (S.groupWidth k tail age + k) f (quota S.rounds)) - k)
  (fitsSigned : e ≤ previous) (fitsCut : previous ≤ S.groupWidth k tail age) (count : Bank)
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


open DescentFallbackPeriod DescentSixParty.Chronology

private theorem middle_le_metadata (out : ResetOutput) (base : ℕ) :
    out.middle.stop base≤out.metadataEnd base := by
  obtain ⟨a₀,a₁,a₂⟩:=out.earlier base
  obtain ⟨a₃,a₄⟩:=out.complete_after base
  have a₅:=out.final_ge base
  have a₆ : out.fullEnd base≤out.roleEnd base := by
    rw [ResetOutput.roleEnd,out.roleTransfer.translate]
    omega
  have a₇ : out.roleEnd base≤out.classEnd base := by
    rw [ResetOutput.classEnd,out.actorClass.translate]
    omega
  have a₈ : out.classEnd base≤out.birthEnd base := by
    rw [ResetOutput.birthEnd,out.birth.translate]
    omega
  have a₉ : out.birthEnd base≤out.primitiveEnd base := by
    rw [ResetOutput.primitiveEnd,out.primitive.translate]
    omega
  have a₁₀ : out.primitiveEnd base≤out.metadataEnd base := by
    rw [ResetOutput.metadataEnd,out.metadata.translate]
    omega
  omega

include fitsStencil fitsSigned fitsCut

theorem named_root_prepared_end : (rc).preparedEnd book=(v).middle.stop base₀ := by
  have half : (a).c/2=cap := by change (2*cap)/2=cap;omega
  have shape : (a).RootShape := by
    refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
    · change 2*cap=2*((a).c/2)
      rw [half]
    · change DescentSignedCableCodec.width venue.degree cap=DescentSignedCableCodec.width venue.degree ((a).c/2)
      rw [half]
  apply (a).prepared_end sh start count io.hubs g (2^n) roots book shape w rfl rfl
  unfold atlasBook
  rw [ResetMiddle.issued_law_width]
  have dim : (E).dim = cc+k := by
    change (cc+k-wide)+wide=cc+k
    exact Nat.sub_add_cancel (Nat.min_le_left _ _)
  rw [dim]
  change (v).middle.rootLawWidth = ResetMiddle.lawWidth venue.degree ((a).c/2) n k (S.hostSize age)
    (2^cc) (2^e) (v).middle.rootField (v).middle.stencil.n (v).middle.stencil.levels (v).middle.stencil.total
  rw [half]; rfl

/-- The inputs are the word width and the published address ceiling of this very date. -/
theorem named_root_pages_fit (pitch : M=2^e)
    (room : ∀t,t∈(v).rootUnits→t*(v).receiver.lanes≤payload/2) (word : payload≤w)
    (ceiling : (a).fullEnd floor<2^w) :
    (rc).preparedEnd book<2^w ∧
    ∀q : RootPage (v).middle.rootDepth (2^(v).middle.rotorBits),
      (v).middle.signedLanes*max (((book).table q).2.field*((book).table q).1)
        ((book).table q).2.outputBits≤w/2 := by
  refine ⟨?_,?_⟩
  · rw [named_root_prepared_end G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count]
    exact (middle_le_metadata _ _).trans_lt ceiling
  · have half : (a).c/2=cap := by change (2*cap)/2=cap;omega
    have layers : (atlas).layerBits=DescentRecordedRotorLayers.width (a).depthCut ((a).c/2) :=rfl
    have lanes : (v).middle.signedLanes=(v).receiver.lanes := by change 2^e=M;exact pitch.symm
    let args := Projected.Receiver.arityLimit (v).middle.rootDegree (2^(v).middle.rootDepth)
      (v).front.donor.cap (v).middle.rotorBits (v).middle.rootDepth
    have inp := room ((v).middle.rootField*args) (by simp [ResetOutput.rootUnits,args])
    have res := room (v).rootOutputBits (by simp [ResetOutput.rootUnits])
    have input : (roots).field*Projected.Receiver.arityLimit (a).ports (2^(v).middle.rootDepth)
        ((a).c/2) (v).middle.rotorBits (v).middle.rootDepth=(v).middle.rootField*args := by
      rw [half]; rfl
    have output : ResetMiddle.rootWord (atlas).board (v).middle.rootDepth (roots).Ht (a).depthCut
        ((a).c/2) (atlas).C (atlas).packet (atlas).instructionBits (atlas).batches=(v).rootOutputBits := by
      change ResetMiddle.rootWord board k Ht f ((a).c/2) C packet (DescentPackedResetRotorRoles.roleBits n)
        (DescentRecordedRotorLayers.layers n packet f ((a).c/2)*ResetInput.calendarLanes S G.b (age+1))=_
      rw [half]; rfl
    apply atlas_lane_room atlas sh start count io.hubs g (2^n) roots layers
    · rw [input,lanes,Nat.mul_comm]
      exact inp.trans (Nat.div_le_div_right word)
    · rw [output,lanes,Nat.mul_comm]
      exact res.trans (Nat.div_le_div_right word)

/-- On the scheduled dyadic cut the public width calibration alone bounds every root page. -/
theorem chosen_root_pages_fit
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e)
    (small : 8*(v).groupWidth≤payload) (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) :
    (rc).preparedEnd book<2^w ∧
    ∀q : RootPage (v).middle.rootDepth (2^(v).middle.rotorBits),
      (v).middle.signedLanes*max (((book).table q).2.field*((book).table q).1)
        ((book).table q).2.outputBits≤w/2 := by
  apply named_root_pages_fit G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count pitch _ word ceiling
  subst M
  subst e
  obtain ⟨rootsEq, receiversEq, _, _⟩ := selected_inventory G S board k tail age p f g drift degree payload
    previous nextM C packet oldLanes primitiveLanes printedBits venue io.wire io.roster floor
  unfold selected at rootsEq receiversEq
  unfold ResetOutput.groupWidth at small
  rw [rootsEq, receiversEq] at small
  intro t ht
  exact selected_room G S board k tail age p f g drift degree payload previous nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor t small (Or.inl ht)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
