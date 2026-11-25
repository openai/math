import OAI.Hierarchy.DescentRegisteredResetSum
import OAI.Hierarchy.DescentResetMetadataChargeBits
import OAI.Hierarchy.DescentResetReceiverDensity
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
/-! # The arity and occupancy checkpoint on the selected chronological reset -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset NativePitch Chronology Filter
open DescentDatedNodeMetadata
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters) (saving : ℕ)

private theorem constant_scale (c J : ℕ) : c≤ scale J c:=
  (Nat.lt_two_pow_self (n:=c)).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))

private theorem scale_mono {e t : ℕ} (J : ℕ) (room : e≤t) : scale J e≤ scale J t:=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right (J+1) room)

private theorem units_at (c : Chart) (args J rate ratio : ℕ) (x : c.blocks≤ scale J rate)
    (n : c.nodes≤ scale J rate) (a : args≤ scale J rate) :
    FinalInputs.metadataUnits c args*ratio≤ scale J (((15+rate)+rate)+rate+ratio):=by
  let L:=scale J rate
  let test : Chart:=⟨L,L,0,0,0,0⟩
  have run : FinalInputs.metadataUnits c args≤FinalInputs.metadataUnits test L:=by
    simp only [FinalInputs.metadataUnits,Chart.inputClock,Chart.inputNames,Chart.loopUnits,Chart.labelUnits,
      Chart.jobs,Chart.names,Chart.tallyWork,test]
    gcongr
  have pos : 1≤L:=Nat.two_pow_pos _
  have sq : L≤L*L:=Nat.le_mul_of_pos_right _ pos
  have cube : L*L≤L*L*L:=Nat.le_mul_of_pos_right _ pos
  have cut : FinalInputs.metadataUnits test L≤(32768*L*L)*L:=by
    simp only [FinalInputs.metadataUnits,Chart.inputClock,Chart.inputNames,Chart.loopUnits,Chart.labelUnits,
      Chart.jobs,Chart.names,Chart.tallyWork,test]
    nlinarith only [pos,sq,cube]
  have k : 32768≤ scale J 15:=Nat.pow_le_pow_right (n:=2) (by decide)
    (Nat.le_mul_of_pos_right 15 (Nat.succ_pos J))
  rw [←scale_mul,←scale_mul,←scale_mul,←scale_mul]
  exact Nat.mul_le_mul ((run.trans cut).trans (Nat.mul_le_mul_right L (Nat.mul_le_mul_right L (Nat.mul_le_mul_right L k)))) (constant_scale ratio J)

theorem metadata : Region G board op K 14 saving:=by
  let ref:=stageNumbers G K.t 0 K.f K.g K.reset 1 0
  let growth:=ResetMiddle.receiptLocalRate G board K.t K.f K.g K.reset K.degree
  let wide:=growth+ref.localTokenExponent+(K.drift+1+operandExponent G ref)
  let fee:=(((15+wide)+wide)+wide)+K.ratio
  let precision:=PhysicalReset.densityRate G board op K.t K.f K.g K.reset K.degree
  let limit:=ResetOutput.receiverRate G board op K.t K.f K.g K.reset K.degree
  refine ⟨1,(growth+fee)+precision,1,2*limit,?_⟩
  intro τ B _ den bought branch
  have cut : 2*limit≤B:=by omega
  filter_upwards [ResetMiddle.receipt_controls_at G board K.t K.f K.g K.reset K.degree τ B den,
    PhysicalReset.scheduled_density G board op K.t K.f K.g K.reset τ K.degree K.drift B den cut branch K.bound,
    PhysicalReset.scheduled_tables G board op K.t K.f K.g K.reset τ K.degree K.drift B den cut branch K.bound,
    FinalInputs.metadata_shared fee saving] with h controls density widths paid
  intro a geom _ J
  let S:=stageNumbers G K.t J K.f K.g K.reset a.copies (tail τ J)
  let k:=groupBits K.t J S.hostGain S.capGain (cutRate K.t K.f K.g)
  let p:=a.position.ports
  let v:=a.hardware.inner.successor
  let u:=v.metadata
  let b:=p.priorStart k a.position.floor
  have control:=controls a.copies a.age a.p 0 0 geom.input
  have rad : 2^k≤ scale J growth:=control.1
  have grow : 2^S.hostGain*S.radix≤ scale J growth:=control.2.2.2.1
  have args:=S.capacities_at_scale G K.drift (K.drift+1) (constant_scale _ J)
  have node : u.chart.nodes≤ scale J wide:=args.1.trans (scale_mono J (show ref.localTokenExponent≤wide by dsimp [wide];omega))
  have operands : v.argumentSlots≤ scale J wide:=args.2.trans (scale_mono J (show K.drift+1+operandExponent G ref≤wide by dsimp [wide];omega))
  have block : u.chart.blocks≤ scale J wide:=rad.trans (scale_mono J (by dsimp [wide];omega))
  have cpu:=units_at u.chart v.argumentSlots J wide K.ratio block node operands
  have hs:=widths a.copies a.age a.p a.degreeLimit a.ordinary p.venue p.operandLanes p.roleLanes b
    p.io.wire p.io.roster geom.input geom.limit geom.degreeAt a.cap geom.precision
  have next:=density a.copies a.age a.p a.degreeLimit a.ordinary p.venue p.operandLanes p.roleLanes b
    p.io.wire p.io.roster geom.live.le geom.input geom.limit geom.degreeAt a.cap geom.precision
  have shapeUnit (z : ResetOutput) : z.nodeBits*z.nodes+z.nodeBits ∈ z.receiverUnits := by
    simp [ResetOutput.receiverUnits]
  have keyUnit (z : ResetOutput) : max z.metadata.paidBits (z.metadata.spanBits+z.metadata.chart.bits) ∈ z.receiverUnits := by
    simp [ResetOutput.receiverUnits]
  have shape : (u.chart.bits*u.chart.nodes+u.chart.bits)*u.chart.lanes≤h/2:=by
    exact hs _ (Or.inr (shapeUnit v))
  have keys : max u.paidBits (u.spanBits+u.chart.bits)*u.chart.lanes≤h/2:=by
    exact hs _ (Or.inr (keyUnit v))
  have out:=paid u.chart u.paidBits u.spanBits v.argumentSlots a.w J a.copies K.ratio (scale J precision)
    (Nat.div_le_self ..) geom.ambient cpu shape keys (Nat.two_pow_pos _) next.1 geom.bus
  let Q:=FinalInputs.metadataUnits u.chart v.argumentSlots*K.ratio
  have raises : u.chart.hosts=S.hostSize a.age*(2^S.hostGain*S.radix):=by
    change S.initialSites*(2^S.hostGain*S.radix)^(a.age+1)=_
    simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have groups : u.chart.groups≤S.groupCount a.age*S.radix:=by
    change S.groupCount (a.age+1)≤S.groupCount a.age*S.radix
    have dec : S.groupCount (a.age+1)≤S.groupCount a.age:=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega : S.length-(a.age+1)≤S.length-a.age))
    exact dec.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have localFee : (2^S.hostGain*S.radix)*Q≤ scale J (growth+fee):= by
    rw [←scale_mul];exact Nat.mul_le_mul grow cpu
  have all : ((2^S.hostGain*S.radix)*Q)*scale J precision≤ scale J ((growth+fee)+precision):= by
    rw [←scale_mul];exact Nat.mul_le_mul_right _ localFee
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 14 = z.metadata := rfl
  rw [charge]
  change FinalInputs.metadataCharge u.chart u.paidBits u.spanBits v.argumentSlots*a.w≤_
  apply out.trans
  rw [raises]
  simp only [one_mul,Sample.hostWork,Sample.groupWork]
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · calc
      _ = S.hostSize a.age*h*((2^S.hostGain*S.radix)*Q):=by ring
      _ ≤ _:=Nat.mul_le_mul_left _ (localFee.trans (scale_mono J (Nat.le_add_right (growth+fee) precision)))
  · calc
      _ = S.hostSize a.age*u.chart.groups*((2^S.hostGain*S.radix)*Q*scale J precision):=by ring
      _ ≤ _:=Nat.mul_le_mul (Nat.mul_le_mul_left _ groups) all

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
