import OAI.Hierarchy.DescentRegisteredNumberCharge
import OAI.Hierarchy.DescentResetReceiptControls
import OAI.Hierarchy.DescentResetRootHeaderScale

namespace OAI
/-! Uniform cofinal price of the authentic ranked numberer, including the
selected donor directories and original coordinate-key table. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPackedWalsh
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

theorem registered_number_tariff (op : RotorSpec) (t f g reset D ratio receiver saving : ℕ) :
    ∃lead exponent : ℕ,∀τ B,0 < B → ∀ᶠ h:ℕ in atTop,∀ copies i p w drift degree s Z : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G t J f g reset copies tb
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(ordinary : ℕ→Dated.Ordinary) (prev : DatePorts) (floor : ℕ)
        (space : ScheduledCodeRoom G S board k tb i p f g drift degree h ordinary op s Z
          prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive),
      let a:=scheduled G S board k tb i p f g drift degree h ordinary op s Z prev.operandLanes prev.roleLanes
        prev.venue prev.io.wire prev.io.roster floor
      let bill:=DatePorts.resetCharges G S board k tb i p f g drift degree h ordinary op s Z prev floor w space
      prev.venue.degree=D → i < S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
      8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
      8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ scale J receiver → a.fullEnd floor < 2^w →
      bill.numbered ≤ S.hostSize i*h*(lead*scale J exponent)+S.hostSize i*(S.groupCount i*S.radix)*
        (lead*scale J exponent)+copies/(2^J)^saving :=by
  let rate:=ResetMiddle.receiptLocalRate G board t f g reset D
  let Ht:=GroupStage.depthBound D n f g
  let Y:=2^n
  let size:=2*((Y+1)+((2*d+4)*Y+(Y+1)*2^(Ht+1)))
  obtain ⟨C,E,quote⟩:=OriginalControlPrice.date_price D Y (2^Ht) (DescentResetCableSlots.cableCap board Ht)
    size rate receiver ratio saving
  refine ⟨C,E,?_⟩
  intro τ B den
  filter_upwards [quote,original_coordinate_key G t f g reset B τ,ResetMiddle.receipt_controls_at G board t f g reset D τ B den]
    with h calculation coordinates controls
  intro copies i p w drift degree s Z J tb S k ordinary prev floor space a bill degreeAt live payload ambient bus bits room width roof
  have height:J ≤ Nat.log 2 h:=Nat.div_le_self ..
  have tailBound:tb ≤ τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ height).trans (by nlinarith))
  have dim:=coordinates copies tb i p payload tailBound live.le
  obtain ⟨block,cap,_,growth,walsh⟩:=controls copies i p 0 0 payload
  apply DatePorts.numbered_charge G S board k tb i p f g drift degree h ordinary op s Z prev floor w space
    rate receiver C E saving _ live rfl rfl dim bits room roof block cap growth walsh width
  intro H G₀ stages X capacity increase b wid rows fee cell count up digits packed read cost one
  exact calculation J H G₀ stages copies X capacity increase b wid rows w fee height ambient cell count up digits packed
    bus read (by simpa only [degreeAt] using cost) one

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
