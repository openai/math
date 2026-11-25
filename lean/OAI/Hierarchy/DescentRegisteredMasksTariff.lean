import OAI.Hierarchy.DescentRegisteredResetCharges
import OAI.Hierarchy.DescentResetSelectedPeerPrice
import OAI.Hierarchy.DescentResetPrivateMaskInvoice
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
/-! Price the three programs of the mask entry on the very same entered reset. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPackedWalsh
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette Filter
open DescentResetLocalRoster
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

private def maskCoefficient (D ht : ℕ) :=
  rosterFactor board ht + 2*CandidateFront.rosterFactor n d ht + D + 1

private theorem mask_controls (D ht J r k : ℕ) (block : 2^k ≤ scale J r) :
    let roots:=rootSlots k (2^n)
    let C:=maskCoefficient board D ht
    let cost:=scale J (2*r+C)
    2^k*(2*(roots*(2^n+2^ht))+2*(roots*DescentResetCableSlots.cableCap board ht)) ≤ cost ∧
      (DescentDenseHostOrder.roster board k ht).card ≤ cost ∧ D ≤ cost ∧ scale J r ≤ cost :=by
  intro roots C cost
  let U:=scale J r
  have one : 1 ≤ U:=Nat.two_pow_pos _
  have fund : C ≤ scale J C:=(Nat.lt_two_pow_self : C < 2^C).le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos J)))
  have exactScale : U*U*scale J C=cost:=by
    rw [show U=scale J r from rfl,scale_mul,scale_mul]; congr 1; omega
  have credit:C*U*U ≤ cost:=by
    rw [←exactScale]; calc C*U*U=U*U*C:=by ring
                           _ ≤ _:=Nat.mul_le_mul_left _ fund
  have positive: 0 < C:=Nat.succ_pos _
  have base:U ≤ C*U*U:=(Nat.le_mul_of_pos_left _ positive).trans (Nat.le_mul_of_pos_right _ one)
  have coeff:C ≤ C*U*U:=(Nat.le_mul_of_pos_right _ one).trans (Nat.le_mul_of_pos_right _ one)
  refine ⟨?_,?_,(show D ≤ C by dsimp [C,maskCoefficient]; omega).trans (coeff.trans credit),base.trans credit⟩
  · apply le_trans _ credit
    have identity : 2^k*(2*(roots*(2^n+2^ht))+2*(roots*DescentResetCableSlots.cableCap board ht))=
        (4*(2^n+2)*(2^n+2^ht+DescentResetCableSlots.cableCap board ht))*2^k*2^k:=by
      dsimp only [roots,rootSlots]; rw [pow_succ 2 k];ring
    rw [identity]
    apply Nat.mul_le_mul _ block
    apply Nat.mul_le_mul _ block
    dsimp only [C,maskCoefficient,rosterFactor]
    omega
  · have dim := DescentDenseHostOrder.roster_bound board k ht
    rw [pow_succ 2 k] at dim
    apply (dim.trans _).trans credit
    calc _ = (2*CandidateFront.rosterFactor n d ht)*2^k :=by unfold CandidateFront.rosterFactor;ring
         _ ≤ C*U:=Nat.mul_le_mul (by dsimp only [C,maskCoefficient];omega) block
         _ ≤ _:=Nat.le_mul_of_pos_right _ one

theorem registered_masks_tariff (op : RotorSpec) (t f g reset D z ratio receiver saving : ℕ) :
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
      rates.board=board → prev.venue.degree=D → i < S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
      8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
      8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ scale J receiver →
      bill.masks ≤ S.hostSize i*h*(lead*scale J exponent)+S.hostSize i*(S.groupCount i*S.radix)*(lead*scale J exponent)
        +3*(copies/(2^J)^saving) :=by
  let rate₀:=ResetMiddle.receiptLocalRate G board t f g reset D
  let ht:=GroupStage.depthBound D n f g
  let rate:=2*rate₀+maskCoefficient board D ht
  obtain ⟨cm,em,quote⟩:=ResetOutput.mask_date_price rate receiver ratio saving
  obtain ⟨cp,ep,privateQuote⟩:=selected_private_mask_invoice G board D f g rate receiver ratio saving
  refine ⟨3*max cm cp,max em ep,?_⟩
  intro τ B den
  filter_upwards [quote,privateQuote,ResetMiddle.receipt_controls_at G board t f g reset D τ B den] with h qm qp ctrl
  intro copies i p w drift degree s Z J tb S k rates ordinary prev floor space a bill atBoard atDeg live payload ambient word bits room units
  let M:=incoming S k tb p f h ordinary (i+1)
  let printed:=printedBits G s Z op
  let u:=DatePorts.innerResetInputs G S rates.board k tb i p f g drift degree h ordinary op s Z prev floor w space
  let v:=a.successor
  let b:=a.rebased (a.stageStart floor)
  let gain:=2^S.hostGain*S.radix
  obtain ⟨block,_,_,growth,low⟩:=ctrl copies i p 0 0 payload
  obtain ⟨jobs₀,shape₀,degree₀,raise⟩:=mask_controls board D ht J rate₀ k block
  have jobs : v.sheets.jobs ≤ scale J rate:=by
    change 2^k*(2*(rootSlots k (2^n)*(2^n+2^GroupStage.depthBound prev.venue.degree n f g))+
      2*(rootSlots k (2^n)*DescentResetCableSlots.cableCap rates.board (GroupStage.depthBound prev.venue.degree n f g))) ≤ _
    simpa only [atBoard,atDeg,ht] using jobs₀
  have shapes : v.front.peer.shapes ≤ scale J rate:=by
    change (DescentDenseHostOrder.roster rates.board k (GroupStage.depthBound prev.venue.degree n f g)).card ≤ _
    rw [atBoard,atDeg]
    exact shape₀
  have oldDegree : v.front.peer.oldDegree ≤ scale J rate:=by change prev.venue.degree ≤ _;simpa only [atDeg] using degree₀
  have blocks:=block.trans raise
  have height : J ≤ Nat.log 2 h:=Nat.div_le_self ..
  have peer:=selected_peer_invoice rates p h drift degree M op.w prev.operandLanes prev.roleLanes printed prev.venue
    prev.io floor u rate receiver ratio saving cm em rfl rfl live bits room jobs oldDegree shapes (growth.trans raise)
    blocks (low.trans raise) units height ambient word qm
  have mask:=selected_mask_invoice rates p h drift degree M op.w prev.operandLanes prev.roleLanes printed prev.venue
    prev.io floor u rate receiver ratio saving cm em rfl rfl live bits room jobs oldDegree shapes (growth.trans raise)
    blocks (low.trans raise) units height ambient word qm
  have quoted:=qp S k tb i p drift degree M op.C op.w prev.operandLanes prev.roleLanes printed w prev.venue prev.io floor
  have privatePrice : v.privateShape.periodPrice*w ≤ S.hostSize i*h*(cp*scale J ep)+
      S.hostSize i*(S.groupCount i*S.radix)*(cp*scale J ep)+copies/(2^J)^saving:=by
    rw [←atBoard] at quoted
    exact quoted rfl rfl live atDeg bits room blocks (low.trans raise) units height ambient word
  let pitch:=v.front.contactLayout (v.actorEnd b)
  let first:=v.jointEnd b
  have priv:=v.privateShape.issued_price first pitch u.earlier.pages w (Nat.two_pow_pos _) (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have pc:instructionWords (v.privateShape.code first pitch u.earlier.pages w)
      (v.privateShape.ticks first pitch u.earlier.pages)*w ≤ _ := (Nat.mul_le_mul_right w priv).trans privatePrice
  let U:=max cm cp*scale J (max em ep)
  have mono (x y : ℕ) (hx:x ≤ max cm cp) (hy:y ≤ max em ep) : x*scale J y ≤ U:=
    Nat.mul_le_mul hx (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hy))
  have common (x y : ℕ) (hx:x ≤ max cm cp) (hy:y ≤ max em ep) :
      S.hostSize i*h*(x*scale J y)+S.hostSize i*(S.groupCount i*S.radix)*(x*scale J y)+copies/(2^J)^saving≤
      S.hostSize i*h*U+S.hostSize i*(S.groupCount i*S.radix)*U+copies/(2^J)^saving:=by
    gcongr <;> exact mono x y hx hy
  have joint:=peer.trans (common cm em (le_max_left ..) (le_max_left ..))
  have rank:=mask.trans (common cm em (le_max_left ..) (le_max_left ..))
  have private_:=pc.trans (common cp ep (le_max_right ..) (le_max_right ..))
  change (_+_+_)*w ≤ _
  rw [Nat.add_mul,Nat.add_mul]
  apply (Nat.add_le_add (Nat.add_le_add joint private_) rank).trans
  dsimp only [U]
  ring_nf
  exact le_rfl

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
