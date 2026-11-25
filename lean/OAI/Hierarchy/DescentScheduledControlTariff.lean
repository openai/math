import OAI.Hierarchy.DescentResetSelectedControlPrice
import OAI.Hierarchy.DescentScheduledVenuePrice
import OAI.Hierarchy.DescentResetClippedDatePrice

namespace OAI
/-! Uniform calendar price of the issued control registers at the current pitch. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentSixParty.Chronology DescentDatedAddressBook DescentPackedWalsh
open DescentPacking.PackedMatch.Local.Stage.Dated DescentResetGates DescentPrimitivePalette
open DescentDatedSeedStartup DescentSIMDLookup DescentNamedFundedChart ProtocolRAM Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false

set_option maxHeartbeats 800000
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

theorem scheduled_control_tariff (t f g reset D receiver ratio saving : ℕ) :
    ∃ lead exponent : ℕ,∀(op : RotorSpec) (drift τ B : ℕ), 0 < B →
      ∀ᶠ h:ℕ in atTop,∀ copies i p w degree s Z oldLanes primitiveLanes : ℕ,
        let J:=Nat.log 2 h/(2*B)
        let tb:=tail τ J
        let S:=stageNumbers G t J f g reset copies tb
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        ∀ (ordinary : ℕ→Ordinary) (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ),
        let _nextM:=incoming S k tb p f h ordinary (i+1)
        let a:=PhysicalReset.scheduled G S board k tb i p f g drift degree h ordinary op s Z oldLanes primitiveLanes
          old io.wire io.roster floor
        let b:=S.localWalshBits p (S.groupWidth k tb i+k) f (quota t)
        i < S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
        old.hosts=S.hostSize i → old.k=k → old.degree=D →
        8*b ≤ h → 8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ TerminalScale.scale J receiver →
        a.successor.controlRegisters.fee*w ≤ S.hostSize i*h*(lead*TerminalScale.scale J exponent)+
          S.hostSize i*(S.groupCount i*S.radix)*(lead*TerminalScale.scale J exponent)+copies/(2^J)^saving := by
  let rate:=ResetMiddle.receiptLocalRate G board t f g reset D
  obtain ⟨lead,exp,quote⟩:=clipped_date_price (ResetOutput.venueLead n d D f g) (3*rate) 3 rate receiver ratio saving
  refine ⟨lead,exp,?_⟩
  intro op drift τ B den
  filter_upwards [quote,ResetMiddle.receipt_controls_at G board t f g reset D τ B den] with h invoice controls
  intro copies i p w degree s Z oldLanes primitiveLanes J tb S k ordinary old io floor a b
    live payload ambient bus origin ownership degreeAt enough roots width
  let nextM := incoming S k tb p f h ordinary (i+1)
  let prev:=resetCut S k tb p f h i
  let printed:=printedBits G s Z op
  let e:=PhysicalReset.receiverCut G S board k tb i p f g drift degree h prev nextM op.C op.w oldLanes primitiveLanes printed old
  let c:=S.groupWidth k tb i
  have size:=controls copies i p e prev payload
  obtain ⟨window,cap,_,growth,bits⟩:=size
  have native:=selected_control_work G S board k tb i p f g drift degree h nextM op.C op.w oldLanes primitiveLanes
    printed old io floor D rate live rfl origin ownership degreeAt roots window cap growth
  have depthAt : S.groupWidth k tb (i+1)=c-k:=by
    have difference:=ResetOutput.next_difference S k tb i live
    dsimp only [c]
    omega
  have oldRows : chunks (S.groupCount i) (2^e)*h ≤ (2+2^k)*h+S.groupCount i*(32*2^k*b+16*a.successor.groupWidth) :=
    board_boundary_rows G S board k tb i p f g drift degree h nextM op.C op.w oldLanes primitiveLanes
      printed old io floor (S.group_power (k:=k) (tail:=tb) rfl rfl i).symm depthAt enough roots
  exact invoice J (S.hostSize i) (S.groupCount i) S.radix copies
    (ResetOutput.venueLead n d D f g*TerminalScale.scale J (3*rate)) (2^k) b a.successor.groupWidth
    (chunks (S.groupCount i) (2^e)) w a.successor.controlRegisters.fee
    (Nat.div_le_self ..) ambient le_rfl window bits width bus oldRows native (Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
