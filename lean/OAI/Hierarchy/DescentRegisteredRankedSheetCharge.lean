import OAI.Hierarchy.DescentResetSelectedRankPrice
import OAI.Hierarchy.DescentResetPublicSlotsRate
import OAI.Hierarchy.DescentResetEvidenceCoefficient
import OAI.Hierarchy.DescentRegisteredResetSample
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
/-! # Ranked and signed sibling budgets on the original registered reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)

noncomputable def rankedSheetCharge :=
  let v:=a.successor
  let b:=a.rebased floor
  let L:=v.rankBook (v.linkedRankInputs u.sectors (v.sheetsStart b)) b
  ((L.clockBudget 7+7*L.textBudget 7)+(L.tailClock v.receiver.capacity 7+7*L.tailText v.receiver.capacity 7))*w
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPackedWalsh
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette Filter
open DescentResetLocalRoster
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

theorem registered_rank_tariff (op : RotorSpec) (t f g reset D z ratio receiver saving : ℕ) :
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
      let u:=DatePorts.innerResetInputs G S rates.board k tb i p f g drift degree h ordinary op s Z prev floor w space
      rates.board=board → prev.venue.degree=D → i < S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
      8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
      8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ scale J receiver →
      u.rankedSheetCharge ≤ S.hostSize i*h*(lead*scale J exponent)+S.hostSize i*(S.groupCount i*S.radix)*(lead*scale J exponent)
        +copies/(2^J)^saving :=by
  let r₀ := ResetMiddle.receiptLocalRate G board t f g reset D
  let ht := GroupStage.depthBound D n f g
  obtain ⟨e,slots⟩:=public_slots_rate board ht r₀
  let shapeC := 2*CandidateFront.rosterFactor n d ht
  let rate := max e (max (g+r₀) (shapeC+r₀))
  obtain ⟨lead,exp,quoted⟩:=ResetOutput.rank_date_price rate receiver ratio saving
  refine ⟨lead,exp,?_⟩
  intro τ B den
  filter_upwards [quoted,ResetMiddle.receipt_controls_at G board t f g reset D τ B den] with h pay ctrl
  intro copies i p w drift degree s Z J tb S k rates ordinary prev floor space a u atBoard atDeg live payload ambient word bits room units
  let v:=a.successor
  let b:=a.rebased (a.stageStart floor)
  let M:=incoming S k tb p f h ordinary (i+1)
  let token:=printedBits G s Z op
  let cap:=((capCalendar G.b S.rounds g S.height).take i).prod*256
  obtain ⟨block,capac,_,growth,low⟩:=ctrl copies i p 0 0 payload
  have mono {i j : ℕ} (small : i ≤ j) : scale J i ≤ scale J j :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ small)
  have scope : r₀ ≤ rate := by dsimp only [rate];omega
  have kBound : v.receiver.candidates ≤ scale J rate := by
    change publicSlots rates.board (GroupStage.depthBound prev.venue.degree n f g) k cap ≤ _
    rw [atBoard,atDeg]
    exact ((slots J k cap block capac).1).trans (mono (Nat.le_max_left ..))
  have cBound : v.receiver.capacity ≤ scale J rate := by
    change 2^g*cap ≤ _
    have base : 2^g ≤ scale J g := Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos J))
    calc _ ≤ scale J g*scale J r₀ := Nat.mul_le_mul base capac
         _ = scale J (g+r₀) := scale_mul ..
         _ ≤ _ := mono (by dsimp only [rate];omega)
  have shapes : v.front.peer.shapes ≤ scale J rate := by
    change (DescentDenseHostOrder.roster rates.board k (GroupStage.depthBound prev.venue.degree n f g)).card ≤ _
    rw [atBoard,atDeg]
    have dim:=DescentDenseHostOrder.roster_bound board k ht
    rw [pow_succ 2 k] at dim
    apply dim.trans
    have coeff : shapeC ≤ scale J shapeC := (Nat.lt_two_pow_self (n := shapeC)).le.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos J)))
    calc _ = shapeC*2^k := by unfold shapeC CandidateFront.rosterFactor;ring
         _ ≤ scale J shapeC*scale J r₀ := Nat.mul_le_mul coeff block
         _ = scale J (shapeC+r₀) := scale_mul ..
         _ ≤ _ := mono (by dsimp only [rate];omega)
  have blocks := block.trans (mono scope)
  exact selected_rank_budget_invoice (i:=i) (w:=w) rates p h drift degree M op.w prev.operandLanes prev.roleLanes
    token prev.venue prev.io floor (v.linkedRankInputs u.sectors (v.sheetsStart b)) b rate receiver ratio
    saving lead exp rfl rfl live bits room blocks kBound cBound shapes (growth.trans (mono scope)) blocks
    (low.trans (mono scope)) units (Nat.div_le_self ..) ambient word pay

end
end Hierarchy.DescentSixParty.NativePitch

namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset NativePitch Chronology Chronology.RegisterTimeline Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters)
local notation "cell" J:arg => groupBits K.t J (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)
local notation "first" a:arg J:arg τ:arg => (stageNumbers G K.t J K.f K.g K.reset (Sample.copies a) (tail τ J)).firstWidth G.b (Sample.p a)
local notation "grain" a:arg J:arg τ:arg => (stageNumbers G K.t J K.f K.g K.reset (Sample.copies a) (tail τ J)).grainAt G.b (Sample.p a) 0

theorem ranked_sheet_charge (saving : ℕ) :
    ∃lead exp share cutoff : ℕ,∀τ B, 0 < τ → 0 < B → 2*τ+cutoff ≤ B →
      G.b ≤ 2^(capRate G K.t K.g) → ∀ᶠ h : ℕ in atTop,∀a : Sample G board op K τ B h,
      a.Geometry → a.ReachedAt →
      let J:=Nat.log 2 h/(2*B)
      a.inputs.rankedSheetCharge ≤ a.hostWork*(lead*scale J exp)+a.groupWork*(lead*scale J exp)+
        share*(a.copies/(2^J)^saving) := by
  obtain ⟨lead,exp,price⟩:=registered_rank_tariff G board op K.t K.f K.g K.reset K.degree K.rate K.ratio K.receiver saving
  refine ⟨lead,exp,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [price τ B den] with h current
  intro a geom _ J
  have quoted:=current a.copies a.age a.p a.w K.drift a.degreeLimit (first a J τ) (grain a J τ) a.rates
  rw [a.boardAt] at quoted
  have bill:=quoted a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space rfl geom.degreeAt geom.live
    geom.input geom.ambient geom.bus geom.walsh geom.root geom.width
  rw [one_mul]
  exact bill

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
