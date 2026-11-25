import OAI.Hierarchy.DescentRegisteredActorCharge
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
/-! The chronological actor opcode on the original calendar has a uniform bit tariff. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPackedWalsh
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

theorem registered_actor_tariff (op : RotorSpec) (t f g reset D z ratio receiver saving : ℕ) :
    ∃lead exponent : ℕ,∀τ B,0 < B → ∀ᶠ h:ℕ in atTop,∀ copies i p w drift degree s Z : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G t J f g reset copies tb
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(rates : ResetRates G S k D n d op.C f g z tb) (ordinary : ℕ→Dated.Ordinary) (prev : DatePorts) (floor : ℕ)
        (space : ScheduledCodeRoom G S rates.board k tb i p f g drift degree h ordinary op s Z
          prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive),
      let a:=scheduled G S rates.board k tb i p f g drift degree h ordinary op s Z prev.operandLanes prev.roleLanes
        prev.venue prev.io.wire prev.io.roster floor
      let bill:=DatePorts.resetCharges G S rates.board k tb i p f g drift degree h ordinary op s Z prev floor w space
      let rhs (lead exponent : ℕ):=S.hostSize i*h*(lead*scale J exponent)+
        S.hostSize i*(S.groupCount i*S.radix)*(lead*scale J exponent)+copies/(2^J)^saving
      rates.board=board → prev.venue.degree=D → i < S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
      8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
      8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ scale J receiver →
      bill.actor ≤ rhs lead exponent := by
  let rate:=ResetMiddle.receiptLocalRate G board t f g reset D
  obtain ⟨lead,exponent,late⟩:=
    ActorSetup.actor_date_price (2^n) d D (GroupStage.depthBound D n f g) rate receiver ratio saving
  refine ⟨lead,exponent,?_⟩
  intro τ B den
  filter_upwards [late,ResetMiddle.receipt_controls_at G board t f g reset D τ B den] with h invoice control
  intro copies i p w drift degree s Z J tb S k rates ordinary prev floor space a bill rhs boardAt degreeAt live payload ambient bus bits rooms width
  obtain ⟨blocks,_,_,_,walsh⟩:=control copies i p 0 0 payload
  have hosts : 0 < S.hostSize i := by
    have source : 0 < copies := (Nat.two_pow_pos _).trans_le ambient
    change 0 < copies*(2^(hostRate t reset)*2^k)^i
    positivity
  exact DatePorts.actor_charge rates i p h drift degree ordinary op s Z prev floor w space
    rate receiver ratio saving lead exponent degreeAt rfl rfl rfl live hosts bits rooms blocks walsh width
    (Nat.div_le_self ..) ambient bus invoice

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
