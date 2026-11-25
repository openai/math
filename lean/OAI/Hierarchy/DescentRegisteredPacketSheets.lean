import OAI.Hierarchy.DescentRegisteredResetSample
import OAI.Hierarchy.DescentNamedPacketFactorScale
import OAI.Hierarchy.DescentResetSelectedReceipt
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
/-! # Both native packet pulls at the registered reset date's word size -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset Chronology
open DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette NativePitch DescentPackedWalsh DescentSIMDLookup Filter
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters)

section
variable {G board op K}

/-- The address is the argument of the operand setup whose two native invoices appear in sheetBill. -/
def Sample.packetInvoice {τ B h : ℕ} (a : Sample G board op K τ B h) (location : ℕ) :=
  let c:=a.hardware.inner.successor.setup
  (c.packets.lane (c.placed location) false).invoice+(c.packets.lane (c.placed location) true).invoice

end

set_option maxRecDepth 16384 in
theorem packet_sheet (saving : ℕ) :
    ∃lead exponent : ℕ,∀τ B,0<B → ∀ᶠ h : ℕ in atTop,∀a : Sample G board op K τ B h,
      a.Geometry → ∀location,
      let J:=Nat.log 2 h/(2*B)
      a.packetInvoice location*a.w≤a.hostWork*(lead*scale J exponent)+
        a.groupWork*(lead*scale J exponent)+a.copies/(2^J)^saving :=by
  let rate:=ResetMiddle.receiptLocalRate G board K.t K.f K.g K.reset K.degree
  obtain ⟨lead,exponent,eventual⟩:=
    clipped_date_price (ResetOutput.packetRateLead K.degree n) (5*rate) 3 rate K.receiver K.ratio saving
  refine ⟨lead,exponent,?_⟩
  intro τ B den
  filter_upwards [eventual,ResetMiddle.receipt_controls_at G board K.t K.f K.g K.reset K.degree τ B den] with h quote controls
  intro a geo location J
  let tb:=tail τ J
  let S:=stageNumbers G K.t J K.f K.g K.reset a.copies tb
  let k:=groupBits K.t J S.hostGain S.capGain (cutRate K.t K.f K.g)
  let i:=a.age
  let prev:=a.position.ports
  let floor:=prev.priorStart k a.position.floor
  let X:=2^k
  let c:=S.groupWidth k tb i
  let raw:=resetCut S k tb a.p K.f h i
  let nextM:=incoming S k tb a.p K.f h a.ordinary (i+1)
  let token:=printedBits G (S.firstWidth G.b a.p) (S.grainAt G.b a.p 0) op
  let e:=receiverCut G S board k tb i a.p K.f K.g K.drift a.degreeLimit h raw nextM op.C op.w prev.operandLanes prev.roleLanes token prev.venue
  let o:=ResetOutput.Prior.atDate G S i a.p K.drift prev.operandLanes prev.roleLanes token prev.venue
  let bits:=S.localWalshBits a.p (c+k) K.f (quota S.rounds)
  let v:=a.hardware.inner.successor
  let before:=a.hardware.inner.rebased (a.hardware.inner.stageStart floor)
  let growth:=2^S.hostGain*S.radix
  obtain ⟨blocks,cap,_,stages,bw⟩:=controls a.copies i a.p e raw geo.input
  have physical : v = ResetOutput.fromBoard G S board k tb i a.p K.f K.g K.drift a.degreeLimit h e raw
      (2^e) nextM op.C op.w o before :=
    PhysicalReset.named_successor G S board k tb i a.p K.f K.g K.drift a.degreeLimit h e raw (2^e)
      nextM op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io.wire prev.io.roster floor
  have inv := PhysicalReset.selected_inventory G S board k tb i a.p K.f K.g K.drift a.degreeLimit h raw nextM
    op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io.wire prev.io.roster floor
  have lanes : v.receiver.lanes = 2^e := inv.2.2.1
  have paidCut : e = v.exponent raw raw (S.groupWidth k tb (i+1)) h := by
    unfold e PhysicalReset.receiverCut ResetOutput.exponent ResetOutput.groupWidth
    rw [show v.rootUnits = _ from inv.1, show v.receiverUnits = _ from inv.2.1]
    rfl
  have key:=keys_fit (m:=min raw (min (laneBits (c+k) h bits-k) (S.groupWidth k tb (i+1)))) v.groupWidth_pos geo.root
  change 1+(v.groupWidth+v.groupWidth)*2^(v.exponent raw raw (S.groupWidth k tb (i+1)) h)≤h/2 at key
  rw [←paidCut,←lanes] at key
  have packed : v.groupWidth*v.receiver.lanes≤h/2:=by rw [Nat.add_mul] at key;omega
  have amount : a.packetInvoice location ≤ v.packetFactor growth*
      ResetOutput.receiptArea h (S.hostSize i) (chunks (S.groupCount i) (2^e)) := by
    change (v.setup.packets.lane (v.setup.placed location) false).invoice +
      (v.setup.packets.lane (v.setup.placed location) true).invoice ≤ _
    rw [physical] at packed ⊢
    exact ResetOutput.packet_volume G S board k tb i a.p K.f K.g K.drift a.degreeLimit h e raw nextM
      op.C op.w o before location rfl geo.live packed
  have coefficient:=ResetOutput.fromBoard_packet_factor G S board k tb i a.p K.f K.g K.drift a.degreeLimit h e raw
    (2^e) nextM op.C op.w o before rate J growth blocks cap stages
  rw [←physical] at coefficient
  change v.packetFactor growth≤ResetOutput.packetRateLead prev.venue.degree n*scale J (5*rate) at coefficient
  rw [geo.degreeAt] at coefficient
  have rs : chunks (S.groupCount i) (2^e)*h≤(2+X)*h+S.groupCount i*(32*X*bits+16*v.groupWidth) := by
    rw [←S.group_power (show S.baseGroups=2^tb from rfl) (show S.radix=2^k from rfl) i]
    have next : S.groupWidth k tb (i+1) = c-k := by
      have step := ResetOutput.next_difference S k tb i geo.live
      change c = S.groupWidth k tb (i+1)+k at step
      omega
    rw [paidCut,next]
    exact v.boundary_rows c k h bits (by dsimp only [bits]; unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega) geo.walsh geo.root
  exact quote J (S.hostSize i) (S.groupCount i) S.radix a.copies (v.packetFactor growth) X bits v.groupWidth
    (chunks (S.groupCount i) (2^e)) a.w (a.packetInvoice location) (Nat.div_le_self ..) geo.ambient
    coefficient blocks bw geo.width geo.bus rs amount (Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
