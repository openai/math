import OAI.Hierarchy.DescentRegisteredContactCharges
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
/-! # Cofinal registered contact costs with constants fixed before the date calendar -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPackedWalsh
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

theorem registered_contact_tariff (op : RotorSpec) (t f g reset D z ratio receiver saving : ℕ) :
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
      bill.contact ≤ rhs lead exponent ∧ bill.classes ≤ rhs lead exponent := by

  let r:=ResetMiddle.receiptLocalRate G board t f g reset D
  let ht:=GroupStage.depthBound D n f g
  let K:=8+D+4*(2^n+2)*(2^n+2^ht)
  let rate:=r+r+K
  obtain ⟨lead,exponent,prices⟩:=DatePorts.contact_amounts rate receiver ratio saving
  refine ⟨lead,exponent,?_⟩
  intro τ B den
  filter_upwards [prices,ResetMiddle.receipt_controls_at G board t f g reset D τ B den] with h quote control
  intro copies i p w drift degree s Z J tb S k rates ordinary prev floor space a bill rhs boardAt deg live payload ambient bus bits rooms width
  let M:=incoming S k tb p f h ordinary (i+1)
  let raw:=resetCut S k tb p f h i
  let e:=receiverCut G S rates.board k tb i p f g drift degree h raw M op.C op.w prev.operandLanes prev.roleLanes
    (printedBits G s Z op) prev.venue
  obtain ⟨blocks,cap,cost,growth,walsh⟩:=control copies i p e raw payload
  let P:=scale J r
  let L:=scale J K
  have pos : 0<P:=Nat.two_pow_pos _
  have coeff: K≤L:=Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right K (Nat.succ_pos _)))
  have ample : P*P*L=scale J rate:=by change scale J r*scale J r*scale J K=scale J ((r+r)+K);rw [scale_mul,scale_mul]
  have pp : P≤P*P:=Nat.le_mul_of_pos_left _ pos
  have ll : 1≤L:=Nat.two_pow_pos _
  have tall : P≤ scale J rate:=pp.trans ((Nat.le_mul_of_pos_right _ ll).trans_eq ample)
  have c : a.successor.contactShape.Controls (scale J rate):=by
    constructor
    · change 2^k*(2*(((capCalendar G.b S.rounds g S.height).take i).prod*256))≤_
      rw [←ample,mul_left_comm (2^k) 2,Nat.mul_comm 2]
      exact Nat.mul_le_mul (Nat.mul_le_mul blocks cap) ((by dsimp only [K];omega : 2≤K).trans coeff)
    · change 2*((2^(k+1)+2^(k+1)*(2^n+1))*(2^n+2^(GroupStage.depthBound prev.venue.degree n f g)))≤_
      rw [deg,←ample]
      simp only [pow_succ]
      calc _=2^k*(4*(2^n+2)*(2^n+2^ht)):=by dsimp only [ht];ring
           _≤P*P*L:=Nat.mul_le_mul (blocks.trans pp) ((by dsimp only [K];omega : 4*(2^n+2)*(2^n+2^ht)≤K).trans coeff)
    · change (DescentDenseHostOrder.roster rates.board k (GroupStage.depthBound prev.venue.degree n f g)).card≤_
      rw [boardAt,deg]
      have palette (names donor : ℕ) : names ≤ CandidateFront.sourceLimit names donor := by
        unfold CandidateFront.sourceLimit
        omega
      exact (palette _ _).trans (cost.trans tall)
    · exact blocks.trans tall
    · change prev.venue.degree≤_
      rw [deg,←ample]
      apply le_trans ((by dsimp only [K];omega : D≤K).trans coeff)
      exact Nat.le_mul_of_pos_left _ (Nat.mul_pos pos pos)
  exact DatePorts.contact_charges p drift degree ordinary op s Z rates h prev floor w space
    rate receiver ratio saving lead exponent live bits rooms c (growth.trans tall) (blocks.trans tall) (walsh.trans tall)
    width (Nat.div_le_self ..) ambient bus quote

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
