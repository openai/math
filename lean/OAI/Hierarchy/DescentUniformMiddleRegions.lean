import OAI.Hierarchy.DescentOriginalMiddleRegions
import OAI.Hierarchy.DescentUniformRootLaw

namespace OAI
/-! # Uniform middle storage over attained reset schedules -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset D drift : ℕ) {ι : ℕ→Type*}
    (index : ℕ→ℕ) (tailCost chosenJ sites age size degree root previous nextM base : ∀h,ι h→ℕ)
    (old : ∀h,ι h→Prior)
local notation "sample" h:arg i:arg => originalSample G op t f g reset (tailCost h i) D drift (chosenJ h i)
  (sites h i) (age h i) (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i)
  (base h i) (old h i)
local notation "z" => fun h i=>sample h i
set_option quotPrecheck false in
local notation "p" => fun h i=>(sample h i).output G board D f g op.C op.w

open DescentPlainTerminal.Suffix DescentSixParty.PackedFlow.Padded
set_option quotPrecheck false in
local notation "count_" h:arg i:arg => (sample h i).sched.groupWidth (sample h i).k (sample h i).tail (sample h i).age

/-- A single address exponent for the complete signed, stencil and ordered-root arrays
over a family of recorded dates with independent epoch lengths and residual depths. -/
theorem uniform_middle (r : CalendarInputs G board D f g op.C op.w index z)
    (level : ∀ᶠ h:ℕ in atTop,index h≤h)
    (oldH : Bounded fun h i=>(sample h i).sched.hostSize (age h i))
    (oldG : Bounded fun h i=>2^(count_ h i))
    (cuts : ∀h i,root h i≤previous h i ∧ previous h i≤count_ h i)
    (halfMatrix : ∀ᶠ h:ℕ in atTop,∀i,let dim:=(count_ h i)+(sample h i).k;dim*dim≤h/2)
    (previousKey : ∀ᶠ h:ℕ in atTop,∀i,(p h i).middle.signedBits*2^(previous h i)≤h/2)
    (priced : Installed p) : MiddleRegions p :=by
  let c j:=Bounded.const (ι:=ι) j
  have M : Bounded fun h i=>2^(root h i):=oldG.of_le fun h i=>
    Nat.pow_le_pow_right (by decide) ((cuts h i).1.trans (cuts h i).2)
  have law:=uniform_sample_root_law G board D f g op.C op.w z (fun _ _=>rfl)
    (fun _ _=>rfl) oldH oldG M priced
  have L:=r.sheets.block.bounded level
  have dims : ∀h i,(p h i).middle.high+(p h i).middle.low=(sample h i).sched.groupWidth (sample h i).k (sample h i).tail (sample h i).age+(sample h i).k:=by
    intro h i
    have e:root h i≤(sample h i).sched.groupWidth (sample h i).k (sample h i).tail (sample h i).age:=(cuts h i).1.trans (cuts h i).2
    change (sample h i).sched.groupWidth (sample h i).k (sample h i).tail (sample h i).age-root h i+(root h i+(sample h i).k)=_
    omega
  have field : Bounded fun h i=>2^(p h i).middle.rootField:=by
    apply Bounded.pow_of_linear (K:=1)
    filter_upwards [priced] with h keys
    intro i
    let v:=p h i
    let N:=DescentFallbackPeriod.Projected.Receiver.arityLimit v.middle.rootDegree (2^v.middle.rootDepth)
      v.front.donor.cap v.middle.rotorBits v.middle.rootDepth
    have fit:=keys i (v.middle.rootField*(N+1)) (.inl (by
      change v.middle.rootField*(N+1) ∈ v.rootUnits
      simp [rootUnits,N]))
    have one:v.middle.rootField≤v.middle.rootField*(N+1):=Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have high:0<v.receiver.lanes:=Nat.two_pow_pos _
    exact one.trans ((Nat.le_mul_of_pos_right _ high).trans (fit.trans (by simpa only [Nat.one_mul] using Nat.div_le_self h 2)))
  have rr:∀h i,(p h i).middle.stencil.r=(sample h i).k:=fun h i=>Nat.add_sub_cancel_left ..
  have widths : ∀ᶠ h:ℕ in atTop,∀i,(p h i).middle.stencil.Widths h:=by
    filter_upwards [priced] with h keys
    intro i
    let a:=(p h i).middle.stencil
    let m:=(sample h i).sched.groupWidth (sample h i).k (sample h i).tail (sample h i).age+(sample h i).k
    let bits:=(sample h i).sched.localWalshBits (size h i) m f (quota t)
    have signed:=keys i (p h i).middle.stencil.n (.inl (by
      change (p h i).middle.stencil.n ∈ (p h i).rootUnits
      simp [rootUnits]))
    have lo : (sample h i).k+bits+2≤h/2 :=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans signed
    have lvl : Nat.clog 2 (m+2)≤ m+2:=Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    apply widths_of_packed a h (Nat.two_pow_pos _) (keys i _ (.inl (by simp [rootUnits,a])))
    change Nat.clog 2 (m+2)+(m+(sample h i).sched.censusBits (size h i))≤h/2
    dsimp [bits,AtomSchedule.localWalshBits,DescentWalshPrecision.bits] at lo
    omega
  have stencil : StencilBook.ScalarRoom (fun h i=>(p h i).middle.stencil):=by
    refine ⟨oldH,oldG,M,L.of_le (fun h i=>Nat.pow_le_pow_right (by decide) (rr h i).le),
      r.dimension.bounded level,c D,1,?_⟩
    filter_upwards [widths] with h w
    intro i
    have ok:=w i
    have small:h/2≤1*h:=by simpa only [Nat.one_mul] using Nat.div_le_self h 2
    exact ⟨ok.layers.trans small,ok.cutoff.trans small,ok.readers.trans small,ok.planes.trans small,ok.gather.trans small⟩
  refine ⟨stencil,L,M,oldG.of_le (fun h i=>Nat.pow_le_pow_right (by decide) ((Nat.sub_le ..).trans (cuts h i).2)),
    (c 2).mul (r.previousCap.bounded level),oldH,(r.dimension.bounded level).of_le (fun h i=>(dims h i).le),
    oldG.of_le (fun _ _=>Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)),oldG,c (2^(GroupStage.depthBound D n f g)),
    field,law,
    ?_,?_,?_⟩
  · filter_upwards [priced] with h keys
    intro i
    let m:=(p h i).middle
    have paid:=keys i ((m.signedBits+m.signedBits)*2^m.rootDepth) (.inl (by
      change (m.signedBits+m.signedBits)*2^m.rootDepth ∈ (p h i).rootUnits
      simp [rootUnits,m]))
    change (m.signedBits+m.signedBits)*2^(root h i+(sample h i).k)≤h/2
    change ((m.signedBits+m.signedBits)*2^(sample h i).k)*2^(root h i) ≤ h/2 at paid
    simpa only [pow_add,Nat.mul_comm (2^(root h i)) (2^((sample h i).k)),Nat.mul_assoc] using paid
  · filter_upwards [halfMatrix] with h good
    intro i
    dsimp only
    rw [dims]
    exact good i
  · filter_upwards [previousKey] with h good
    intro i
    change (p h i).middle.signedBits*(2^(previous h i-root h i)*2^(root h i))≤h/2
    rw [←pow_add,Nat.sub_add_cancel (cuts h i).1]
    exact good i

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
