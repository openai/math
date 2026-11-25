import OAI.Hierarchy.DescentRegisteredSheetParts
import OAI.Hierarchy.DescentRegisteredResetPrimitiveRegions
import OAI.Hierarchy.DescentOriginalLookupLimits
import OAI.Hierarchy.DescentResetSelectedLookupVolume
import OAI.Hierarchy.DescentResetSignedPlacementVolume

namespace OAI
/-! Registered cost of the original local lookup passes and the compact signed-slot placement. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset Chronology
open DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette NativePitch DescentPackedWalsh DescentSIMDLookup Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters)

private theorem scale_le {j a b : ℕ} (h : a≤b) : scale j a≤ scale j b :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h)

set_option maxHeartbeats 400000 in
set_option maxRecDepth 32768 in
theorem local_sheet (slot : Bool) (saving : ℕ) :
    ∃lead exponent share cutoff : ℕ,∀τ B,0<τ→0<B→2*τ+cutoff≤B→G.b≤2^(capRate G K.t K.g)→
      ∀ᶠ h : ℕ in atTop,∀a : Sample G board op K τ B h,a.Geometry→a.ReachedAt→
      let J:=Nat.log 2 h/(2*B)
      a.sheetCost (if slot then 4 else 0)≤a.hostWork*(lead*scale J exponent)+
        a.groupWork*(lead*scale J exponent)+share*(a.copies/(2^J)^saving):=by
  let rate:=ResetMiddle.receiptLocalRate G board K.t K.f K.g K.reset K.degree
  let lp:=ResetOutput.lookupLocalExponent G board op K.t K.f K.g K.reset K.degree
  let pr:=ResetOutput.primitiveLocalExponent G board op K.t K.f K.g K.reset K.degree
  let R:=lp+pr+rate
  let P:=30+4*(lp+1)+rate+3*R
  obtain ⟨lead,exponent,late⟩:=clipped_date_price 1000000 P 3 rate K.receiver K.ratio saving
  refine ⟨lead,exponent,1,0,?_⟩
  intro τ B _ den _ branch
  filter_upwards [late,ResetMiddle.receipt_controls_at G board K.t K.f K.g K.reset K.degree τ B den,
    ResetOutput.original_lookup_limits G board op K.t K.f K.g K.reset K.degree τ K.drift B den branch K.bound,
    ResetOutput.original_primitive_limits G board op K.t K.f K.g K.reset K.degree τ K.drift B den branch K.bound]
    with h estimate controls bookLimits primitiveLimits
  intro a geo _ J
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
  have sampleEq : (sampleOriginal a).output G board K.degree K.f K.g op.C op.w = v := original_output a geo
  have physical : v = ResetOutput.fromBoard G S board k tb i a.p K.f K.g K.drift a.degreeLimit h e raw
      (2^e) nextM op.C op.w o before :=
    PhysicalReset.named_successor G S board k tb i a.p K.f K.g K.drift a.degreeLimit h e raw (2^e)
      nextM op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io.wire prev.io.roster floor
  have facts:v.LookupLimits a.inputs.headerWork (scale J lp):=by
    change v.LookupLimits (37+28*(v.front.signedQueries/2)) _
    rw [←sampleEq]
    exact bookLimits a.copies i a.p a.degreeLimit e raw (2^e) nextM before o geo.input geo.limit
  have orig:v.PrimitiveLimits (scale J pr) growth 100:=by
    rw [←sampleEq]
    exact primitiveLimits a.copies i a.p a.degreeLimit e raw (2^e) nextM before o geo.input geo.limit
  have inv := PhysicalReset.selected_inventory G S board k tb i a.p K.f K.g K.drift a.degreeLimit h raw nextM
    op.C op.w prev.operandLanes prev.roleLanes token prev.venue prev.io.wire prev.io.roster floor
  have seed : 8*v.groupWidth≤h := geo.root
  unfold ResetOutput.groupWidth at seed
  rw [show v.rootUnits = _ from inv.1, show v.receiverUnits = _ from inv.2.1] at seed
  have fit (t : ℕ) (hx:t∈v.rootUnits ∨ t∈v.receiverUnits) : t*2^e≤h/2 := by
    have funded := PhysicalReset.selected_room G S board k tb i a.p K.f K.g K.drift a.degreeLimit h raw nextM op.C op.w
      prev.operandLanes prev.roleLanes token prev.venue prev.io.wire prev.io.roster floor t seed hx
    rw [inv.2.2.1] at funded
    exact funded
  have rs : chunks (S.groupCount i) (2^e)*h≤(2+X)*h+S.groupCount i*(32*X*bits+16*v.groupWidth) := by
    rw [←S.group_power (show S.baseGroups=2^tb from rfl) (show S.radix=2^k from rfl) i]
    have paidCut : e = v.exponent raw raw (S.groupWidth k tb (i+1)) h := by
      unfold e PhysicalReset.receiverCut ResetOutput.exponent ResetOutput.groupWidth
      rw [show v.rootUnits = _ from inv.1, show v.receiverUnits = _ from inv.2.1]
      rfl
    have next : S.groupWidth k tb (i+1) = c-k := by
      have step := ResetOutput.next_difference S k tb i geo.live
      change c = S.groupWidth k tb (i+1)+k at step
      omega
    rw [paidCut,next]
    exact v.boundary_rows c k h bits (by dsimp only [bits]; unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega) geo.walsh geo.root
  let T:=ResetOutput.receiptArea h (S.hostSize i) (chunks (S.groupCount i) (2^e))
  have native₀ : v.sheetLookups v.receiver.candidates a.inputs.headerWork≤(v.lookupFactor a.inputs.headerWork*growth)*T := by
    rw [physical]
    exact ResetOutput.selected_lookup_volume G S board k tb i a.p K.f K.g K.drift a.degreeLimit h e raw nextM
      op.C op.w o before a.inputs.headerWork rfl geo.live (fun t ht=>fit t (.inr (by rw [physical];exact ht)))
  have native₄ : v.setup.placement.invoice v.setup.signedFields 7≤v.signedPlacementFactor growth*T := by
    rw [physical]
    exact ResetOutput.signed_placement_volume G S board k tb i a.p K.f K.g K.drift a.degreeLimit h e raw nextM
      op.C op.w o before rfl geo.live (fun t ht=>fit t (by rw [physical];exact ht))
  have localBound:v.lookupFactor a.inputs.headerWork*growth≤1000000*scale J P:=by
    apply (Nat.mul_le_mul (v.lookup_factor_rate lp J _ facts) stages).trans
    have eq:scale J (30+4*(lp+1))*scale J rate=scale J (30+4*(lp+1)+rate):=by
      unfold scale
      rw [←pow_add]
      congr 1
      ring
    rw [eq]
    exact (scale_le (by dsimp [P];omega)).trans (Nat.le_mul_of_pos_left _ (by decide : 0<1000000))
  have signedBound:v.signedPlacementFactor growth≤1000000*scale J P:=by
    have small:scale J lp≤ scale J R:=scale_le (by dsimp [R];omega)
    have shapes:scale J pr≤ scale J R:=scale_le (by dsimp [R];omega)
    have N:v.setup.strip≤ scale J R:=by
      apply le_trans _ (facts.inputs.trans small)
      unfold DescentResetOperandSetup.Chart.inputs
      omega
    apply (v.signed_factor_bound growth J R N (facts.blocks.trans small) (orig.shapes.trans shapes)
      (orig.gain.trans shapes)).trans
    exact Nat.mul_le_mul_left _ (scale_le (by dsimp [P];omega))
  have cost (fee factor:ℕ) (native:fee≤factor*T) (local_:factor≤1000000*scale J P) :=
    estimate J (S.hostSize i) (S.groupCount i) S.radix a.copies factor X bits v.groupWidth
      (chunks (S.groupCount i) (2^e)) a.w fee (Nat.div_le_self ..) geo.ambient local_ blocks bw
      geo.width geo.bus rs native (Nat.two_pow_pos k)
  have hostUnits : a.hostWork=S.hostSize i*h := rfl
  have groupUnits : a.groupWork=S.hostSize i*(S.groupCount i*S.radix) := rfl
  rw [hostUnits,groupUnits]
  cases slot
  · change (v.sheetLookups v.receiver.candidates a.inputs.headerWork)*a.w ≤ _
    simpa only [one_mul] using cost _ _ native₀ localBound
  · change (v.setup.placement.invoice v.setup.signedFields 7)*a.w ≤ _
    simpa only [one_mul] using cost _ _ native₄ signedBound
end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
