import OAI.Hierarchy.DescentRegisteredFundingRoom
import OAI.Hierarchy.DescentRegisteredResetCharges
import OAI.Hierarchy.DescentResetRootHeaderScale
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
/-! Charge the original funded reset, from the previous normalized writable
page through the signed row regroup and new compact funded census. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPackedWalsh
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette DescentSIMDLookup Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

private theorem sourcePalette (names donor : ℕ) : names ≤ CandidateFront.sourceLimit names donor := by
  unfold CandidateFront.sourceLimit
  omega

theorem registered_funding_tariff (op : RotorSpec) (t f g reset D z ratio receiver saving : ℕ) :
    ∃ lead exponent : ℕ,∀τ B,0 < B → ∀ᶠ h:ℕ in atTop,∀ copies i p w drift degree s Z : ℕ,
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
      rates.board=board → prev.venue.degree=D → i < S.length → i%(S.rounds+1)=S.rounds →
      p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
      prev.venue.hosts=S.hostSize i → prev.venue.groups=S.groupCount i → prev.venue.k=k →
      prev.venue.paidBits=S.censusBits p → prev.venue.lanes=incoming S k tb p f h ordinary i →
      prev.venue.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256 →
      8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
      8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ scale J receiver →
      bill.funding ≤ S.hostSize i*h*(lead*scale J exponent)+S.hostSize i*(S.groupCount i*S.radix)*
        (lead*scale J exponent)+copies/(2^J)^saving := by
  let r₀:=ResetMiddle.receiptLocalRate G board t f g reset D
  let rate:=4+2*r₀+receiver
  obtain ⟨C,E,late⟩:=FinalInputs.funding_date_price 2000000 (2*rate) (6+2*rate) ratio saving
  refine ⟨C,E,?_⟩
  intro τ B den
  filter_upwards [late,original_coordinate_key G t f g reset B τ,
    ResetMiddle.receipt_controls_at G board t f g reset D τ B den] with h quote dims controls
  intro copies i p w drift degree s Z J tb S k rates ordinary prev floor space a bill boardAt deg live atReset
    payload ambient bus hosts groups blocks prec lanes capacity localRoom rootRoom width
  let M:=incoming S k tb p f h ordinary (i+1)
  let printed:=printedBits G s Z op
  let c:=S.groupWidth k tb i
  let b:=S.localWalshBits p (c+k) f (quota t)
  let raw:=resetCut S k tb p f h i
  let e:=receiverCut G S rates.board k tb i p f g drift degree h raw M op.C op.w prev.operandLanes
    prev.roleLanes printed prev.venue
  let U:=scale J r₀
  let top:=scale J rate
  have mono {x y : ℕ} (le : x ≤ y) : scale J x ≤ scale J y:=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)
  have localFits:U ≤ top:=mono (by dsimp [rate];omega)
  have unitFits:scale J receiver ≤ top:= mono (by dsimp [rate];omega)
  have height:J ≤ Nat.log 2 h:=Nat.div_le_self ..
  have bound:tb ≤ τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ height).trans (by nlinarith))
  have dimension:=dims copies tb i p payload bound live.le
  have square:(c+k)*(c+k) ≤ h/2:=by
    change (c+k+1)^2 ≤ h/2 at dimension
    nlinarith only [dimension,Nat.zero_le (c+k)]
  obtain ⟨window,oldCap,source,_,digits⟩:=controls copies i p e raw payload
  have size:c+k ≤ b:=by dsimp only [b];unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  have handles : a.successor.venue.census.jobs ≤ U := by
    change (DescentDenseHostOrder.roster rates.board k (GroupStage.depthBound prev.venue.degree n f g)).card ≤ U
    rw [boardAt,deg]
    exact (sourcePalette _ _).trans source
  have pitch:prev.venue.lanes=2^raw:=lanes.trans (by simp only [raw,incoming,ite_eq_left live,ite_eq_left atReset])
  obtain ⟨oldLane,newLane,oldKey,axes,packed,join,flag,census⟩:=funding_keys_at G S rates.board k tb i p f g
    drift degree h M op.C op.w prev.operandLanes prev.roleLanes printed prev.venue prev.io floor live blocks prec
    pitch capacity localRoom rootRoom square
  have volume:=walsh_rows (c:=c) (k:=k) (h:=h) (b:=b)
    (by dsimp only [b];unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega) localRoom
  have sixteen:16 ≤ scale J 4:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_mul_of_pos_right 4 (Nat.succ_pos J))
  have factor:16*2^k*b ≤ top:=calc
    _ ≤ (scale J 4*U)*U:=Nat.mul_le_mul (Nat.mul_le_mul sixteen window) digits
    _ = scale J (4+r₀+r₀):=by rw [scale_mul,scale_mul]
    _ ≤ top:=mono (by dsimp [rate];omega)
  have sites:prev.venue.groups=2^c:=groups.trans (S.group_power (k:=k) (tail:=tb) rfl rfl i).symm
  have prior : chunks prev.venue.groups prev.venue.lanes*h ≤ h+prev.venue.groups*top :=by
    rw [sites,pitch]
    exact volume.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ factor) h)
  exact selected_funding_invoice rates p h drift degree M op.w prev.operandLanes prev.roleLanes printed
    prev.venue prev.io floor w rate ratio saving C E rfl rfl live hosts groups blocks localRoom rootRoom
    (window.trans localFits) (digits.trans localFits) (width.trans unitFits) (size.trans (digits.trans localFits))
    (handles.trans localFits) (by rw [capacity]; exact oldCap.trans localFits) prior oldLane newLane oldKey axes packed join flag
    census height ambient bus quote

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
