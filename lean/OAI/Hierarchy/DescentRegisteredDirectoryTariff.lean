import OAI.Hierarchy.DescentRegisteredResetCharges
import OAI.Hierarchy.DescentResetSelectedCompactTrunk
import OAI.Hierarchy.DescentResetSelectedReceipt
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
/-! The received bank and its following compact tables, at the original public
calendar's operand addresses. The two components have separate charges. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPackedWalsh
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

attribute [local irreducible] CandidateFront.sourceLimit

theorem registered_directory_tariff (op : RotorSpec) (t f g reset D z ratio receiver saving : ℕ) :
    ∃cr er cc ec : ℕ,∀τ B,0 < B → ∀ᶠ h:ℕ in atTop,∀ copies i p w drift degree s Z : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G t J f g reset copies tb
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(rates : ResetRates G S k D n d op.C f g z tb) (ordinary : ℕ→Dated.Ordinary) (prev : DatePorts) (floor : ℕ)
        (space : ScheduledCodeRoom G S rates.board k tb i p f g drift degree h ordinary op s Z
          prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive),
      let a:=PhysicalReset.scheduled G S rates.board k tb i p f g drift degree h ordinary op s Z prev.operandLanes prev.roleLanes
        prev.venue prev.io.wire prev.io.roster floor
      let bill:=DatePorts.resetCharges G S rates.board k tb i p f g drift degree h ordinary op s Z prev floor w space
      let rhs (lead exponent : ℕ):=S.hostSize i*h*(lead*scale J exponent)+
        S.hostSize i*(S.groupCount i*S.radix)*(lead*scale J exponent)+copies/(2^J)^saving
      rates.board=board → prev.venue.degree=D → i < S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
      8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
      8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ scale J receiver →
      bill.received ≤ rhs cr er ∧ bill.compact ≤ rhs cc ec := by
  let rate:=ResetMiddle.receiptLocalRate G board t f g reset D
  obtain ⟨cr,er,received⟩:=ResetOutput.receipt_date_price board D f g rate receiver ratio saving
  obtain ⟨cc,ec,compact⟩:=clipped_date_price 32768 rate 0 rate receiver ratio saving
  refine ⟨cr,er,cc,ec,?_⟩
  intro τ B den
  filter_upwards [received,compact,ResetMiddle.receipt_controls_at G board t f g reset D τ B den] with h rq cq control
  intro copies i p w drift degree s Z J tb S k rates ordinary prev floor space a bill rhs boardAt deg live payload ambient bus bits rooms width
  let M:=incoming S k tb p f h ordinary (i+1)
  let printed:=printedBits G s Z op
  let raw:=resetCut S k tb p f h i
  let e:=receiverCut G S rates.board k tb i p f g drift degree h raw M op.C op.w prev.operandLanes prev.roleLanes printed prev.venue
  have sizes:=control copies i p e raw payload
  obtain ⟨blocks,cap,cost,growth,walsh⟩:=sizes
  have paid:0 < S.hostSize i:=by
    have source:0 < copies:=(Nat.two_pow_pos _).trans_le ambient
    change 0 < copies*(2^(hostRate t reset)*2^k)^i
    positivity
  have sourceWork:CandidateFront.sourceLimit a.successor.front.peer.shapes
      (500+23*a.successor.middle.stencil.m+64) ≤ scale J rate := by
    change CandidateFront.sourceLimit (DescentDenseHostOrder.roster rates.board k
      (GroupStage.depthBound prev.venue.degree n f g)).card (500+23*(S.groupWidth k tb i+k)+64) ≤ _
    let limit (B₀ : NonlinearExpanders.Graph n d) (D₀ : ℕ) :=
      CandidateFront.sourceLimit (DescentDenseHostOrder.roster B₀ k (GroupStage.depthBound D₀ n f g)).card
        (500+23*(S.groupWidth k tb i+k)+64)
    have aligned : limit rates.board prev.venue.degree = limit board D :=
      congrArg₂ limit boardAt deg
    exact aligned.le.trans cost
  constructor
  · apply selected_received_invoice (i:=i) rates p h drift degree M op.w prev.operandLanes prev.roleLanes printed
      prev.venue prev.io floor prev.archive.count w rate receiver ratio saving cr er rfl rfl live paid bits rooms
      blocks cap sourceWork growth walsh width (Nat.div_le_self ..) ambient bus _ space.scene
    rw [boardAt,deg]
    exact rq
  · exact selected_compact_trunk_invoice (i:=i) rates p h drift degree M op.w prev.operandLanes prev.roleLanes printed
      prev.venue prev.io floor w rate receiver ratio saving cc ec rfl rfl live bits rooms blocks walsh growth width
      (Nat.div_le_self ..) ambient bus cq

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
