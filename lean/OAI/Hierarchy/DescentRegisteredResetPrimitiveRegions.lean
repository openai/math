import OAI.Hierarchy.DescentRegisteredResetSample
import OAI.Hierarchy.DescentRegisteredResetSum
import OAI.Hierarchy.DescentOriginalMoverUnits
import OAI.Hierarchy.DescentOriginalMoverApertures
import OAI.Hierarchy.DescentResetReceiverDensity
import OAI.Hierarchy.DescentRegisteredNumberTariff

namespace OAI
/-! # Calendar prices of retained primitive movement and newly issued roles -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset NativePitch Chronology Chronology.RegisterTimeline Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (K : Parameters)
local notation "rate" => ResetOutput.primitiveLocalExponent G board op K.t K.f K.g K.reset K.degree
local notation "recRate" => ResetMiddle.receiptLocalRate G board K.t K.f K.g K.reset K.degree
local notation "ρ" => ResetOutput.receiverRate G board op K.t K.f K.g K.reset K.degree
local notation "δ" => densityRate G board op K.t K.f K.g K.reset K.degree
local notation "S_" a:arg j:arg τ:arg => stageNumbers G K.t j K.f K.g K.reset (Sample.copies a) (tail τ j)
local notation "k_" j:arg => groupBits K.t j (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)
local notation "v_" a:arg => (Sample.hardware a).inner.successor
local notation "at_" a:arg => (Sample.hardware a).inner.rebased ((Sample.hardware a).inner.stageStart (Sample.hardware a).priorStart)
local notation "old_" a:arg => (Sample.position a).ports

private theorem leScale {a b j : ℕ} (le:a≤b):scale j a≤ scale j b:=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)

private theorem mulScale (a b j : ℕ):scale j a*scale j b=scale j (a+b):=by
  unfold scale
  rw [Nat.add_mul,pow_add]

private theorem constantScale (u j : ℕ):u≤ scale j u:=
  (Nat.lt_two_pow_self (n:=u)).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))

private theorem extend {v : ResetOutput} {a b inc work : ℕ} (s:v.PrimitiveLimits a inc work) (larger:a≤b) :
    v.PrimitiveLimits b inc work:=⟨s.nodes.trans larger,s.args.trans larger,s.roots.trans larger,
  s.residual.trans larger,s.shapes.trans larger,s.blocks.trans larger,s.finalNodes.trans larger,
  s.finalBlocks.trans larger,s.gain.trans larger,s.source.trans larger⟩

section
variable {G board op K} {τ B h : ℕ} (a : Sample G board op K τ B h)
local notation "J" => Nat.log 2 h/(2*B)
local notation "S" => S_ a J τ
local notation "k" => k_ J
local notation "O" => old_ a
local notation "s" => (S).firstWidth G.b a.p
local notation "grain" => (S).grainAt G.b a.p 0
local notation "token" => DescentPrimitivePalette.printedBits G s grain op
local notation "M" => incoming (S) k (tail τ J) a.p K.f h a.ordinary (a.age+1)
local notation "cut" => resetCut (S) k (tail τ J) a.p K.f h a.age
local notation "prior" => ResetOutput.Prior.atDate G (S) a.age a.p K.drift (O).operandLanes (O).roleLanes token (O).venue
local notation "e" => receiverCut G (S) board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h cut M
    op.C op.w (O).operandLanes (O).roleLanes token (O).venue

def sampleOriginal:=ResetOutput.originalSample G op K.t K.f K.g K.reset τ K.degree K.drift J
  a.copies a.age a.p a.degreeLimit h e cut (2^e) M (at_ a) prior

theorem original_output (g:a.Geometry) :
    (sampleOriginal a).output G board K.degree K.f K.g op.C op.w=v_ a:=by
  let raw := ResetOutput.fromBoard G (S) board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h e cut (2^e) M
    op.C op.w prior (at_ a)
  have output : (v_ a) = raw := PhysicalReset.named_successor G (S) board k (tail τ J) a.age a.p K.f K.g
    K.drift a.degreeLimit h e cut (2^e) M op.C op.w (O).operandLanes (O).roleLanes token (O).venue
    (O).io.wire (O).io.roster ((O).priorStart k a.position.floor)
  rw [output]
  let recorded := {(O).venue with
    degree := K.degree
    cap := ((capCalendar G.b K.t K.g J).take a.age).prod*256
    paidBits := (S).censusBits a.p}
  have venue : recorded = (O).venue := by
    dsimp only [recorded]
    rw [←g.degreeAt, ←g.precision, ←a.cap]
  change ResetOutput.fromBoard G (S) board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h e cut (2^e) M
    op.C op.w ({prior with venue:=recorded}) (at_ a) = raw
  rw [venue]
  rfl

private theorem prior_nodes : (prior).nodes≤(S).retainedNodes:=by
  change (if a.age=0 then 1 else (S).retainedNodes)≤_
  split
  · exact Nat.pow_pos (Nat.two_pow_pos _)
  · rfl

private theorem roots_shape (g:a.Geometry)
    (room:∀sites age p degree e' prev lanes next start old,p≤h→degree≤K.bound→
      let z:=ResetOutput.originalSample G op K.t K.f K.g K.reset τ K.degree K.drift J sites age p degree h e' prev lanes next start old
      ResetOutput.PrimitiveLimits (z.output G board K.degree K.f K.g op.C op.w) (scale J rate) (2^z.sched.hostGain*z.sched.radix) 100) :
    ResetOutput.PrimitiveLimits (v_ a) (scale J rate) (2^(S).hostGain*(S).radix) 100:=by
  rw [←original_output a g]
  exact room a.copies a.age a.p a.degreeLimit e cut (2^e) M (at_ a) prior g.input g.limit
private theorem mover_aperture (geo : a.Geometry)
    (square : ((S).groupWidth k (tail τ J) a.age+k)*((S).groupWidth k (tail τ J) a.age+k) ≤ h/2) :
    (v_ a).roleTransfer.pitches.Apertures h := by
  let issued := ResetOutput.fromBoard G (S) board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h e cut (2^e) M
    op.C op.w prior (at_ a)
  have output : (v_ a) = issued := PhysicalReset.named_successor G (S) board k (tail τ J) a.age a.p K.f K.g
    K.drift a.degreeLimit h e cut (2^e) M op.C op.w (O).operandLanes (O).roleLanes token (O).venue
    (O).io.wire (O).io.roster ((O).priorStart k a.position.floor)
  have archive := geo.archiveWidths.roles
  rw [geo.archiveWidths.nodes] at archive
  have purchased : token*(prior).nodes*(O).roleLanes ≤ h/2 := archive
  have old : issued.roleTransfer.transfer.wholeWord*issued.roleTransfer.transfer.previousLanes ≤ h/2 := purchased
  have ppos : 0 < (prior).nodes := by
    change 0 < (if a.age=0 then 1 else (S).retainedNodes)
    split
    · decide
    · exact Nat.pow_pos (Nat.two_pow_pos _)
  have bitpos : 0 < token := by
    apply Nat.clog_pos (by decide : 1<2)
    unfold DescentPrimitivePalette.colors
    omega
  have oldPitch : issued.roleTransfer.transfer.previousLanes ≤ h :=
    (Nat.le_mul_of_pos_left (O).roleLanes (Nat.mul_pos bitpos ppos)).trans (purchased.trans (Nat.div_le_self ..))
  have inv := PhysicalReset.selected_inventory G (S) board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h
    cut M op.C op.w (O).operandLanes (O).roleLanes token (O).venue (O).io.wire (O).io.roster ((O).priorStart k a.position.floor)
  let seed := ResetOutput.fromBoard G (S) board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h 0 cut 1 M
    op.C op.w prior 0
  have width : (v_ a).groupWidth = seed.groupWidth := by
    have roots : (v_ a).rootUnits = seed.rootUnits := inv.1
    have receivers : (v_ a).receiverUnits = seed.receiverUnits := inv.2.1
    unfold ResetOutput.groupWidth
    rw [roots, receivers]
  have seedRoom : 8*seed.groupWidth ≤ h := width ▸ geo.root
  have room : 8*issued.groupWidth ≤ h := output ▸ geo.root
  have paid (t : ℕ) (hit : t ∈ issued.rootUnits ∨ t ∈ issued.receiverUnits) : t*2^e ≤ h/2 := by
    rw [← output] at hit
    have fits := PhysicalReset.selected_room G (S) board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h
      cut M op.C op.w (O).operandLanes (O).roleLanes token (O).venue (O).io.wire (O).io.roster
      ((O).priorStart k a.position.floor) t seedRoom hit
    rwa [inv.2.2.1] at fits
  rw [output]
  exact ResetOutput.original_mover_apertures G (S) board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h
    e cut M op.C op.w prior (at_ a) (prior_nodes a) old oldPitch square room paid

end

theorem birth (saving : ℕ) : Region G board op K 13 saving:=by
  obtain ⟨C,E,offer⟩:=ResetOutput.primitive_date_price (rate+recRate) K.receiver K.ratio saving
  refine ⟨C,E,1,0,?_⟩
  intro τ B _ den _ branch
  filter_upwards [offer,ResetOutput.original_primitive_limits G board op K.t K.f K.g K.reset K.degree τ K.drift B den branch K.bound,
    ResetMiddle.receipt_controls_at G board K.t K.f K.g K.reset K.degree τ B den] with h priced room bands
  intro a geo _ J
  let S:=S_ a J τ
  let k:=k_ J
  let u:=a.position.ports
  let M:=incoming S k (tail τ J) a.p K.f h a.ordinary (a.age+1)
  let token:=DescentPrimitivePalette.printedBits G (S.firstWidth G.b a.p) (S.grainAt G.b a.p 0) op
  have actual:=extend (roots_shape a geo room) (leScale (Nat.le_add_right rate recRate))
  obtain ⟨blocks,_,_,_,walsh⟩:=bands a.copies a.age a.p 0 0 geo.input
  have q:=selected_primitive_invoice (i:=a.age) a.rates a.p h K.drift a.degreeLimit M op.w u.operandLanes u.roleLanes token u.venue u.io
    (u.priorStart k a.position.floor) a.w (rate+recRate) K.receiver K.ratio saving C E
  rw [a.boardAt] at q
  have paid:=q rfl rfl geo.live geo.walsh geo.root actual
    (blocks.trans (leScale (Nat.le_add_left recRate rate))) (walsh.trans (leScale (Nat.le_add_left recRate rate)))
    geo.width (Nat.div_le_self ..) geo.ambient geo.bus priced
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 13 = z.birth := rfl
  rw [charge, one_mul]
  change ((v_ a).birth.invoice + ((v_ a).primitive.clockBound (FinalInputs.originBudget a.hardware.inner) +
    7*(v_ a).primitive.nameBound (FinalInputs.originBudget a.hardware.inner)))*a.w ≤ _
  exact paid

set_option maxHeartbeats 800000 in
theorem mover (saving : ℕ) : Region G board op K 11 saving:=by
  let coefficient:=64+8*rate+K.ratio
  let degree:=rate+δ+K.receiver+K.archive+9
  refine ⟨256,coefficient+(degree+degree),1,2*ρ,?_⟩
  intro τ B _ den bought branch
  filter_upwards [ResetOutput.original_primitive_limits G board op K.t K.f K.g K.reset K.degree τ K.drift B den branch K.bound,
    ResetOutput.original_mover_units G board op K.t K.f K.g K.reset K.degree τ K.drift B den branch K.bound,
    PhysicalReset.scheduled_density G board op K.t K.f K.g K.reset τ K.degree K.drift B den (by omega) branch K.bound,
    original_coordinate_key G K.t K.f K.g K.reset B τ,selected_mover_literal coefficient saving] with h shapes tariffs pitches coordinate share
  intro a geo _ J
  let S:=S_ a J τ
  let k:=k_ J
  let u:=a.position.ports
  let M:=incoming S k (tail τ J) a.p K.f h a.ordinary (a.age+1)
  let token:=DescentPrimitivePalette.printedBits G (S.firstWidth G.b a.p) (S.grainAt G.b a.p 0) op
  let raw:=resetCut S k (tail τ J) a.p K.f h a.age
  let e:=receiverCut G S board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h raw M op.C op.w
    u.operandLanes u.roleLanes token u.venue
  let prior:=ResetOutput.Prior.atDate G S a.age a.p K.drift u.operandLanes u.roleLanes token u.venue
  let V:=v_ a
  let T:=V.roleTransfer
  let inc:=2^S.hostGain*S.radix
  let rhs:=scale J degree
  have actual:=roots_shape a geo shapes
  have height:J≤Nat.log 2 h:=Nat.div_le_self ..
  have tailRoom:tail τ J≤τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ height).trans (by nlinarith))
  have dim:=coordinate a.copies (tail τ J) a.age a.p geo.input tailRoom geo.live.le
  have square:(S.groupWidth k (tail τ J) a.age+k)*(S.groupWidth k (tail τ J) a.age+k)≤h/2:=by
    change (S.groupWidth k (tail τ J) a.age + k + 1)^2 ≤ h/2 at dim
    rw [pow_two] at dim
    exact (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)).trans dim
  have aperture : T.pitches.Apertures h := mover_aperture a geo square
  have inv:T.invoiceUnits≤2^64*scale J (8*rate):=by
    change (v_ a).roleTransfer.invoiceUnits≤_
    rw [←original_output a geo]
    exact tariffs a.copies a.age a.p a.degreeLimit e raw (2^e) M (at_ a) prior geo.input geo.limit (prior_nodes a)
  have units:T.invoiceUnits*K.ratio≤ scale J coefficient:=by
    calc
      _≤(scale J 64*scale J (8*rate))*scale J K.ratio:=Nat.mul_le_mul
        (inv.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos J)))))
        (constantScale K.ratio J)
      _=_:=by rw [mulScale,mulScale]
  obtain ⟨now,rootNow,_⟩:=pitches a.copies a.age a.p a.degreeLimit a.ordinary u.venue u.operandLanes u.roleLanes
    (u.priorStart k a.position.floor) u.io.wire u.io.roster geo.live.le geo.input geo.limit geo.degreeAt a.cap geo.precision
  have rootDensity:S.groupCount (a.age+1)≤T.rootLanes ∨ h≤T.rootLanes*scale J δ:=by
    have lanesEq : T.rootLanes = V.receiver.lanes := rootNow
    rw [lanesEq]
    exact now
  have q:=selected_mover_invoice (i:=a.age) a.rates a.p h K.drift a.degreeLimit M op.w u.operandLanes u.roleLanes token
    u.venue u.io (u.priorStart k a.position.floor) a.w (scale J K.archive) (scale J δ) (scale J δ)
    K.ratio coefficient saving
  rw [a.boardAt] at q
  have paid:=q rfl rfl geo.live aperture geo.rolePositive geo.archiveDensity.roles rootDensity now height geo.ambient
    geo.bus units (share J a.copies height geo.ambient)
  have gg:inc≤rhs:=actual.gain.trans (leScale (by dsimp [degree];omega))
  have xx:T.placement.blocks≤rhs:=actual.blocks.trans (leScale (by dsimp [degree];omega))
  have nr:scale J δ≤rhs:=leScale (by dsimp [degree];omega)
  have prev:scale J K.archive≤rhs:=leScale (by dsimp [degree];omega)
  have uu:V.retainedRoleUnit≤rhs:=((V.groupWidth_fit (t:=V.retainedRoleUnit) (Or.inr (by simp [ResetOutput.receiverUnits]))).trans geo.width).trans
    (leScale (by dsimp [degree];omega))
  have rp:1≤rhs:=Nat.two_pow_pos _
  have s1:T.pitches.hostRate inc≤256*(rhs*rhs):=by
    change 10+T.placement.blocks+inc≤_
    nlinarith [Nat.mul_le_mul rp rp,Nat.mul_le_mul_left rhs rp]
  have s2:DescentRetainedSeven.Chart.fieldRate inc (scale J K.archive) V.retainedRoleUnit (scale J δ) (scale J δ)≤256*(rhs*rhs):=by
    unfold DescentRetainedSeven.Chart.fieldRate
    calc _≤rhs+112*rhs+rhs+(1+rhs)*rhs:=by gcongr
         _≤_:=by nlinarith [Nat.mul_le_mul_left rhs rp]
  have scaled {z : ℕ} (p:z≤256*(rhs*rhs)) : T.invoiceUnits*K.ratio*z≤256*scale J (coefficient+(degree+degree)):=by
    calc
      _ ≤ scale J coefficient * (256 * (rhs * rhs)) := Nat.mul_le_mul units p
      _ = 256 * (scale J coefficient * (rhs * rhs)) := by ac_rfl
      _ = _ := by rw [show rhs * rhs = scale J (degree + degree) from mulScale .., mulScale]
  have rad : S.groupCount a.age≤S.groupCount a.age*S.radix:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 11 = z.mover := rfl
  rw [charge, one_mul]
  change T.invoice ((v_ a).fullEnd (at_ a)) a.w*a.w ≤ _
  exact paid.trans (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left _ (scaled s1)) (Nat.mul_le_mul (Nat.mul_le_mul_left _ rad) (scaled s2))) _)

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
