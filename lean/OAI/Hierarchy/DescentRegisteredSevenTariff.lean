import OAI.Hierarchy.DescentRegisteredSheetParts
import OAI.Hierarchy.DescentRegisteredResetPrimitiveRegions
import OAI.Hierarchy.DescentInitialArgumentCapacity
import OAI.Hierarchy.DescentOriginalSevenDimensions
import OAI.Hierarchy.DescentOriginalSevenApertures
import OAI.Hierarchy.DescentResetSelectedSevenPrice

namespace OAI
/-! # Calendar price of copying the seven true operand fields on reset -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset NativePitch Chronology Chronology.RegisterTimeline Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (K : Parameters)
local notation "rate" => ResetOutput.primitiveLocalExponent G board op K.t K.f K.g K.reset K.degree
local notation "ρ" => ResetOutput.receiverRate G board op K.t K.f K.g K.reset K.degree
local notation "δ" => densityRate G board op K.t K.f K.g K.reset K.degree
local notation "k_" j => groupBits K.t j (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)
local notation "v_" a => (Sample.hardware a).inner.successor
local notation "at_" a => (Sample.hardware a).inner.rebased ((Sample.hardware a).inner.stageStart (Sample.hardware a).priorStart)
local notation "old_" a => (Sample.position a).ports

private theorem widenSeven {a b j : ℕ} (le:a≤b):scale j a≤ scale j b:=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)

private theorem multiplySeven (a b j : ℕ):scale j a*scale j b=scale j (a+b):=by
  unfold scale
  rw [Nat.add_mul,pow_add]

private theorem fixedSeven (u j : ℕ):u≤ scale j u:=
  (Nat.lt_two_pow_self (n:=u)).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))

private theorem seven_host_bound {blocks growth bound : ℕ}
    (positive : 1 ≤ bound) (hb : blocks ≤ bound) (hg : growth ≤ bound) :
    10 + blocks + growth ≤ 256 * (bound * bound) := by
  nlinarith [Nat.mul_le_mul_left bound positive]

private theorem seven_field_bound {growth old retained packet bound : ℕ}
    (positive : 1 ≤ bound) (hg : growth ≤ bound) (ho : old ≤ bound)
    (hr : retained ≤ bound) (hp : packet ≤ bound) :
    DescentRetainedSeven.Chart.fieldRate growth old retained packet packet ≤ 256 * (bound * bound) := by
  unfold DescentRetainedSeven.Chart.fieldRate
  calc
    _ ≤ bound+112*bound+bound+(1+bound)*bound := by gcongr
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_left bound positive]

set_option maxHeartbeats 500000 in
theorem seven_sheet (saving : ℕ) :
    ∃lead exponent share cutoff : ℕ,∀τ B,0<τ→0<B→2*τ+cutoff≤B→G.b≤2^(capRate G K.t K.g)→
      ∀ᶠ h:ℕ in atTop,∀a : Sample G board op K τ B h,a.Geometry→a.ReachedAt→
      let J:=Nat.log 2 h/(2*B)
      a.sheetCost 3≤a.hostWork*(lead*scale J exponent)+a.groupWork*(lead*scale J exponent)+
        share*(a.copies/(2^J)^saving):=by
  obtain ⟨vRate,rateRoom⟩:=DescentRetainedSeven.fixed_units rate
  obtain ⟨j₀,threshold⟩:=Filter.eventually_atTop.1 rateRoom
  let coefficient:=vRate+K.ratio
  let degree:=rate+δ+K.receiver+K.archive+9
  refine ⟨256,coefficient+(degree+degree),1,2*ρ,?_⟩
  intro τ B _ den bought branch
  filter_upwards [ResetOutput.original_primitive_limits G board op K.t K.f K.g K.reset K.degree τ K.drift B den branch K.bound,
    ResetOutput.original_seven_dimensions G board op K.t K.f K.g K.reset K.degree τ K.drift B den branch K.bound,
    PhysicalReset.scheduled_density G board op K.t K.f K.g K.reset τ K.degree K.drift B den (by omega) branch K.bound,
    original_coordinate_key G K.t K.f K.g K.reset B τ,selected_mover_literal coefficient saving,eventually_late (max 1 j₀) B den] with h shapes dimensions pitches coordinate share jbig
  intro a geo _ J
  let S := stageNumbers G K.t J K.f K.g K.reset a.copies (tail τ J)
  let k:=k_ J
  let u:=a.position.ports
  let M:=incoming S k (tail τ J) a.p K.f h a.ordinary (a.age+1)
  let token:=DescentPrimitivePalette.printedBits G (S.firstWidth G.b a.p) (S.grainAt G.b a.p 0) op
  let raw:=resetCut S k (tail τ J) a.p K.f h a.age
  let e:=receiverCut G S board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h raw M op.C op.w
    u.operandLanes u.roleLanes token u.venue
  let prior:=ResetOutput.Prior.atDate G S a.age a.p K.drift u.operandLanes u.roleLanes token u.venue
  let V:=v_ a
  let T:=V.setup.seven
  let inc:=2^S.hostGain*S.radix
  let rhs:=scale J degree
  have actual:V.PrimitiveLimits (scale J rate) inc 100:=by
    change ResetOutput.PrimitiveLimits (v_ a) _ _ _
    rw [←original_output a geo]
    exact shapes a.copies a.age a.p a.degreeLimit e raw (2^e) M (at_ a) prior geo.input geo.limit
  have priorSize:=DescentSixParty.AtomSchedule.prior_capacity S G a.age a.p K.drift u.operandLanes u.roleLanes token u.venue
    (show 0<S.height from (Nat.le_max_left 1 j₀).trans jbig) branch
  have height:J≤Nat.log 2 h:=Nat.div_le_self ..
  have tailRoom:tail τ J≤τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ height).trans (by nlinarith))
  have dim:=coordinate a.copies (tail τ J) a.age a.p geo.input tailRoom geo.live.le
  have square:(S.groupWidth k (tail τ J) a.age+k)*(S.groupWidth k (tail τ J) a.age+k)≤h/2:=by
    change (S.groupWidth k (tail τ J) a.age+k+1)^2 ≤ h/2 at dim
    rw [pow_two] at dim
    exact (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)).trans dim
  have pword : T.retained.wholeWord*T.retained.previousLanes≤h/2:=by
    have q:=geo.archiveWidths.operands
    rw [geo.archiveWidths.digits,geo.archiveWidths.nodes] at q
    exact q
  have ppos:0<prior.nodes:=by
    change 0<(if a.age=0 then 1 else S.retainedNodes)
    split
    · decide
    · exact Nat.pow_pos (Nat.two_pow_pos _)
  have bitpos:0<DescentOperandWidth.recordBits G S k (tail τ J) K.drift a.degreeLimit a.p:=
    (Nat.succ_pos (Nat.log 2 a.p)).trans_le (Nat.le_max_right ..)
  have laneroom:u.operandLanes≤h:=(Nat.le_mul_of_pos_left u.operandLanes (Nat.mul_pos bitpos ppos)).trans
    (pword.trans (Nat.div_le_self ..))
  let issued := ResetOutput.fromBoard G S board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h e raw (2^e) M
    op.C op.w prior (at_ a)
  have output : V = issued := PhysicalReset.named_successor G S board k (tail τ J) a.age a.p K.f K.g
    K.drift a.degreeLimit h e raw (2^e) M op.C op.w u.operandLanes u.roleLanes token u.venue
    u.io.wire u.io.roster (u.priorStart k a.position.floor)
  have inventory := PhysicalReset.selected_inventory G S board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h
    raw M op.C op.w u.operandLanes u.roleLanes token u.venue u.io.wire u.io.roster (u.priorStart k a.position.floor)
  let seed := ResetOutput.fromBoard G S board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h 0 raw 1 M
    op.C op.w prior 0
  have seedWidth : V.groupWidth = seed.groupWidth := by
    have roots : V.rootUnits = seed.rootUnits := inventory.1
    have receivers : V.receiverUnits = seed.receiverUnits := inventory.2.1
    unfold ResetOutput.groupWidth
    rw [roots, receivers]
  have seedRoom : 8*seed.groupWidth ≤ h := seedWidth ▸ geo.root
  have room : 8*issued.groupWidth ≤ h := output ▸ geo.root
  have issuedLanes (t : ℕ) (hit : t ∈ issued.rootUnits ∨ t ∈ issued.receiverUnits) : t*2^e ≤ h/2 := by
    rw [←output] at hit
    have fits := PhysicalReset.selected_room G S board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h
      raw M op.C op.w u.operandLanes u.roleLanes token u.venue u.io.wire u.io.roster
      (u.priorStart k a.position.floor) t seedRoom hit
    rwa [inventory.2.2.1] at fits
  have aperture : T.Apertures h := by
    have old : V.setup.seven.retained.wholeWord*V.setup.seven.retained.previousLanes ≤ h/2 := pword
    have pitch : V.setup.seven.retained.previousLanes ≤ h := laneroom
    change V.setup.seven.Apertures h
    rw [output] at old pitch ⊢
    exact ResetOutput.original_seven_apertures G S board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h
      e raw M op.C op.w prior (at_ a) priorSize.1 priorSize.2 rfl rfl geo.live old pitch square room issuedLanes
  obtain ⟨lim,chartAt⟩:=dimensions a.copies a.age a.p a.degreeLimit e raw (2^e) M (at_ a) prior geo.input geo.limit priorSize.1 priorSize.2
  have same:lim.chart=T:=chartAt.trans (congrArg (fun v:ResetOutput=>v.setup.seven) (original_output a geo))
  have inv:T.units 7≤ scale J vRate:=same ▸ threshold J ((Nat.le_max_right 1 j₀).trans jbig) lim
  have units:T.units 7*K.ratio≤ scale J coefficient:=
    (Nat.mul_le_mul inv (fixedSeven K.ratio J)).trans_eq (multiplySeven vRate K.ratio J)
  obtain ⟨now,rootNow,_⟩:=pitches a.copies a.age a.p a.degreeLimit a.ordinary u.venue u.operandLanes u.roleLanes
    (u.priorStart k a.position.floor) u.io.wire u.io.roster geo.live.le geo.input geo.limit geo.degreeAt a.cap geo.precision
  have density : S.groupCount (a.age+1) ≤ V.receiver.lanes ∨ h ≤ V.receiver.lanes*scale J δ := now
  have rootLanes : V.middle.rootLanes = V.receiver.lanes := rootNow
  have rootDensity : S.groupCount (a.age+1) ≤ T.packetLanes ∨ h ≤ T.packetLanes*scale J δ := by
    change S.groupCount (a.age+1) ≤ V.middle.rootLanes ∨ h ≤ V.middle.rootLanes*scale J δ
    rw [rootLanes]
    exact density
  have q:=selected_seven_invoice (i:=a.age) a.rates a.p h K.drift a.degreeLimit M op.w u.operandLanes u.roleLanes token
    u.venue u.io (u.priorStart k a.position.floor) a.w (scale J K.archive) (scale J δ) (scale J δ)
    K.ratio coefficient saving
  rw [a.boardAt] at q
  have paid:=q rfl rfl geo.live aperture geo.argPositive geo.archiveDensity.operands rootDensity now height geo.ambient
    geo.bus units (share J a.copies height geo.ambient)
  have gg:inc≤rhs:=actual.gain.trans (widenSeven (by dsimp [degree];omega))
  have xx:T.placement.blocks≤rhs:=actual.blocks.trans (widenSeven (by dsimp [degree];omega))
  have nr:scale J δ≤rhs:=widenSeven (by dsimp [degree];omega)
  have prev:scale J K.archive≤rhs:=widenSeven (by dsimp [degree];omega)
  have uu:V.retainedUnit≤rhs:=((V.groupWidth_fit (t:=V.retainedUnit) (Or.inr (by simp [ResetOutput.receiverUnits]))).trans geo.width).trans
    (widenSeven (by dsimp [degree];omega))
  have rp:1≤rhs:=Nat.two_pow_pos _
  have s1 : T.hostRate inc ≤ 256*(rhs*rhs) := seven_host_bound rp xx gg
  have s2 : DescentRetainedSeven.Chart.fieldRate inc (scale J K.archive) V.retainedUnit
      (scale J δ) (scale J δ) ≤ 256*(rhs*rhs) := seven_field_bound rp gg prev uu nr
  have scaled {z : ℕ} (hz : z≤256*(rhs*rhs)) : T.units 7*K.ratio*z≤256*scale J (coefficient+(degree+degree)) := by
    calc
      _ ≤ scale J coefficient * (256 * (rhs * rhs)) := Nat.mul_le_mul units hz
      _ = 256 * (scale J coefficient * (rhs * rhs)) := by ac_rfl
      _ = _ := by rw [show rhs * rhs = scale J (degree+degree) from multiplySeven .., multiplySeven]
  have rad : S.groupCount a.age≤S.groupCount a.age*S.radix:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
  rw [one_mul]
  change T.invoice (V.operandFloor (at_ a)) a.w 7 * a.w ≤ _
  exact paid.trans (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left _ (scaled s1)) (Nat.mul_le_mul (Nat.mul_le_mul_left _ rad) (scaled s2))) _)

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
