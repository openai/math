import OAI.Hierarchy.DescentResetSelectedVenueWork
import OAI.Hierarchy.DescentResetVenueDatePrice
import OAI.Hierarchy.DescentCalibratedIncomingVolume
import OAI.Hierarchy.DescentScheduledResetChart

namespace OAI
/-! Complete outgoing price at the reset's physical private pitch and its genuine
next chronological pitch, including the last dated venue's successor. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentSixParty.Chronology DescentDatedAddressBook DescentPackedWalsh
open DescentPacking.PackedMatch.Local.Stage.Dated DescentResetGates DescentPrimitivePalette
open DescentDatedSeedStartup DescentSIMDLookup DescentNamedFundedChart ProtocolRAM Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false

section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail i p f g drift degree h nextM C packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "prev" => resetCut S k tail p f h i
local notation "e" => PhysicalReset.receiverCut G S board k tail i p f g drift degree h prev nextM C packet oldLanes primitiveLanes printedBits old
local notation "date" => PhysicalReset.selected G S board k tail i p f g drift degree h prev nextM C packet oldLanes primitiveLanes
  printedBits old io.wire io.roster floor
local notation "v" => (date).successor

private theorem inventory_exponent {chosen seed : ResetOutput} (previous transform next h : ℕ)
    (roots : chosen.rootUnits = seed.rootUnits) (receivers : chosen.receiverUnits = seed.receiverUnits) :
    chosen.exponent previous transform next h = seed.exponent previous transform next h := by
  unfold ResetOutput.exponent ResetOutput.groupWidth
  rw [roots, receivers]

private theorem board_root_exponent : (v).exponent prev prev (S.groupWidth k tail (i+1)) h = e := by
  have inv := PhysicalReset.selected_inventory G S board k tail i p f g drift degree h prev nextM C
    packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  exact inventory_exponent prev prev (S.groupWidth k tail (i+1)) h inv.1 inv.2.1

theorem board_boundary_rows
    (groupPow : S.groupCount i = 2^(S.groupWidth k tail i))
    (widthStep : S.groupWidth k tail (i+1)=S.groupWidth k tail i-k)
    (enough : 8*S.localWalshBits p (S.groupWidth k tail i+k) f (quota S.rounds) ≤ h)
    (roots : 8*(v).groupWidth ≤ h) :
    DescentSIMDLookup.chunks (S.groupCount i) (2^e)*h ≤ (2+2^k)*h+S.groupCount i*(32*2^k*(S.localWalshBits p (S.groupWidth k tail i+k) f (quota S.rounds))+16*(v).groupWidth) := by
  have fixed := board_root_exponent G S board k tail i p f g drift degree h nextM C packet oldLanes primitiveLanes printedBits old io floor
  rw [groupPow, ←fixed, widthStep]
  exact (v).boundary_rows _ k h _ (by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega) enough roots

end

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

theorem scheduled_venue_date_tariff (t f g reset D receiver ratio saving : ℕ) :
    ∃ nextRate lead exponent : ℕ,∀(op : RotorSpec) (drift τ B : ℕ), nextRate+2 ≤ B →
      G.b ≤ 2^(capRate G t g) → 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19)) ≤ B →
      ∀ᶠ h:ℕ in atTop,∀ copies i p w degree s Z oldLanes primitiveLanes : ℕ,
        let J:=Nat.log 2 h/(2*B)
        let tb:=tail τ J
        let S:=stageNumbers G t J f g reset copies tb
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        ∀ (ordinary : ℕ→Ordinary) (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ),
        let a:=PhysicalReset.scheduled G S board k tb i p f g drift degree h ordinary op s Z oldLanes primitiveLanes
          old io.wire io.roster floor
        let b:=S.localWalshBits p (S.groupWidth k tb i+k) f (quota t)
        i < S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
        (∀j<S.length,j%(S.rounds+1)≠S.rounds→(ordinary j).payload=h ∧ (ordinary j).unit=(DonorDate.atDate G S g k j p).amount) →
        old.hosts=S.hostSize i → old.k=k → old.degree=D →
        8*b ≤ h → 8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ scale J receiver →
        a.successor.venue.fee*w ≤ S.hostSize i*h*(lead*scale J exponent)+
          S.hostSize i*(S.groupCount i*S.radix)*(lead*scale J exponent)+copies/(2^J)^saving := by
  let rate:=ResetMiddle.receiptLocalRate G board t f g reset D
  obtain ⟨nextRate,nextCost⟩:=dated_volume G t f g reset
  obtain ⟨lead,ex,quote⟩:=venue_date_price (ResetOutput.venueLead n d D f g) (3*rate) rate receiver nextRate ratio saving
  refine ⟨nextRate,lead,ex,?_⟩
  intro op drift τ B room branch terminal
  have den:0 < B:=by omega
  filter_upwards [quote,nextCost op drift τ B room branch terminal,
    ResetMiddle.receipt_controls_at G board t f g reset D τ B den] with h invoice price controls
  intro copies i p w degree s Z oldLanes primitiveLanes J tb S k ordinary old io floor a b
    live payload ambient bus calibrated origin ownership degreeAt enough roots width
  let nextM := incoming S k tb p f h ordinary (i+1)
  let prev:=resetCut S k tb p f h i
  let printed:=printedBits G s Z op
  let e:=PhysicalReset.receiverCut G S board k tb i p f g drift degree h prev nextM op.C op.w oldLanes primitiveLanes printed old
  let c:=S.groupWidth k tb i
  have size:=controls copies i p e prev payload
  obtain ⟨window,cap,_,growth,bits⟩:=size
  obtain ⟨_,next,covered⟩:=price copies p (i+1) (S.hostSize i) ordinary payload calibrated
  have native:=selected_venue_work G S board k tb i p f g drift degree h nextM op.C op.w oldLanes primitiveLanes printed
    old io floor D rate live rfl origin ownership degreeAt next roots window cap growth
  have sg:S.groupCount (i+1)*(2^k)=S.groupCount i:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits live (show S.radix=2^k from rfl))).symm
  have fewer:S.groupCount (i+1) ≤ S.groupCount i:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq sg
  have pos:0 < S.hostSize i:=by
    have initial:0 < copies:=(Nat.two_pow_pos h).trans_le ambient
    change 0 < copies*(2^(hostRate t reset)*2^k)^i
    positivity
  have depthAt : S.groupWidth k tb (i+1)=c-k:=by
    have difference:=ResetOutput.next_difference S k tb i live
    dsimp only [c]
    omega
  have oldRows:chunks (S.groupCount i) (2^e)*h ≤ (2+2^k)*h+S.groupCount i*(32*2^k*b+16*a.successor.groupWidth):=by
    exact board_boundary_rows G S board k tb i p f g drift degree h nextM op.C op.w oldLanes
      primitiveLanes printed old io floor (S.group_power (k:=k) (tail:=tb) rfl rfl i).symm
      depthAt enough roots
  exact invoice J (S.hostSize i) (S.groupCount i) (S.groupCount (i+1)) S.radix copies
    (ResetOutput.venueLead n d D f g*TerminalScale.scale J (3*rate)) (2^k) b a.successor.groupWidth
    (chunks (S.groupCount i) (2^e)) (chunks (S.groupCount (i+1)) nextM) w a.successor.venue.fee
    (Nat.div_le_self ..) ambient le_rfl window bits width bus oldRows covered fewer pos native (Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
