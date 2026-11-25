import OAI.Hierarchy.DescentDatedStencilFromWidth
import OAI.Hierarchy.DescentOriginalRootLawRegion
import OAI.Hierarchy.DescentOriginalPeerRegions
import OAI.Hierarchy.DescentDatedStencilRate

namespace OAI
/-! # Earlier signed, stencil, and privately allocated root arrays on the selected calendar -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G:PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ D drift B : ℕ) {ι : ℕ→Type*}
variable (sites age size degree root previous nextM base : ∀h,ι h→ℕ) (old : ∀h,ι h→Prior)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "a_" h:arg i:arg => originalSample G op t f g reset τ D drift (J_ h) (sites h i) (age h i)
  (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i) (base h i) (old h i)
set_option quotPrecheck false in
local notation "out_" => fun h i=>(a_ h i).output G board D f g op.C op.w


open DescentPlainTerminal.Suffix DescentSixParty.PackedFlow.Padded
set_option quotPrecheck false in
local notation "c_" h:arg i:arg => (S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i)

structure MiddleRegions (p : ∀h,ι h→ResetOutput) : Prop where
  stencil : StencilBook.ScalarRoom (fun h i=>(p h i).middle.stencil)
  blocks : Bounded (fun h i=>(p h i).middle.oldBlocks)
  lanes : Bounded (fun h i=>(p h i).middle.signedLanes)
  ratio : Bounded (fun h i=>(p h i).middle.signedRatio)
  ports : Bounded (fun h i=>(p h i).middle.signedPorts)
  hosts : Bounded (fun h i=>(p h i).middle.signedHosts)
  dimension : Bounded (fun h i=>(p h i).middle.high+(p h i).middle.low)
  high : Bounded (fun h i=>2^(p h i).middle.high)
  rootGroups : Bounded (fun h i=>(p h i).middle.rootGroups)
  shapes : Bounded (fun h i=>(p h i).middle.rootShapes)
  field : Bounded (fun h i=>2^(p h i).middle.rootField)
  law : Bounded (fun h i=>(p h i).middle.rootLawWidth)
  word : ∀ᶠ h:ℕ in atTop,∀i,let m:=(p h i).middle;(m.signedBits+m.signedBits)*2^m.low≤h/2
  matrix : ∀ᶠ h:ℕ in atTop,∀i,let m:=(p h i).middle;(m.high+m.low)*(m.high+m.low)≤h/2
  retile : ∀ᶠ h:ℕ in atTop,∀i,let m:=(p h i).middle;m.signedBits*(m.signedRatio*m.signedLanes)≤h/2

theorem original_middle (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (bound : ℕ)
    (short : ∀h i,size h i≤h) (degrees : ∀h i,degree h i≤bound)
    (seed : Bounded sites) (earlier : ∀h i,age h i≤(S_ h i).length)
    (cuts : ∀h i,root h i≤previous h i ∧ previous h i≤c_ h i)
    (next : ∀h i,root h i≤(S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i+1))
    (previousKey : ∀ᶠ h:ℕ in atTop,∀i,(out_ h i).middle.signedBits*2^(previous h i)≤h/2)
    (priced : Installed (out_)) : MiddleRegions (out_) :=by
  let p:=out_
  let c j:=Bounded.const (ι:=ι) j
  have axes:=schedule_space G t f g reset τ B sites age seed earlier
  have cal:=original_inputs G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees
  have height : ∀ᶠ h:ℕ in atTop,J_ h≤h :=Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have oldG : Bounded (fun h i=>2^(c_ h i)):=axes.oldGroup.of_le fun h i=>((S_ h i).group_power (k:=k_ h) rfl rfl _).le
  have M:Bounded (fun h i=>2^(root h i)):=oldG.of_le fun h i=>Nat.pow_le_pow_right (by decide) ((cuts h i).1.trans (cuts h i).2)
  have L:=cal.sheets.block.bounded height
  have dims : ∀h i,(p h i).middle.high+(p h i).middle.low=c_ h i+k_ h:=by
    intro h i
    have e:root h i≤c_ h i:=(cuts h i).1.trans (cuts h i).2
    change c_ h i-root h i+(root h i+k_ h)=_
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
  have rr:∀h i,(p h i).middle.stencil.r=k_ h:=fun h i=>Nat.add_sub_cancel_left ..
  have widths : ∀ᶠ h:ℕ in atTop,∀i,(p h i).middle.stencil.Widths h:=by
    filter_upwards [priced] with h keys
    intro i
    let a:=(p h i).middle.stencil
    let m:=c_ h i+k_ h
    let bits:=(S_ h i).localWalshBits (size h i) m f (quota t)
    have signed:=keys i (p h i).middle.stencil.n (.inl (by
      change (p h i).middle.stencil.n ∈ (p h i).rootUnits
      simp [rootUnits]))
    have lo : k_ h+bits+2≤h/2 :=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans signed
    have lvl : Nat.clog 2 (m+2)≤ m+2:=Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    apply widths_of_packed a h (Nat.two_pow_pos _) (keys i _ (.inl (by simp [rootUnits,a,p])))
    change Nat.clog 2 (m+2)+(m+(S_ h i).censusBits (size h i))≤h/2
    dsimp [bits,AtomSchedule.localWalshBits,DescentWalshPrecision.bits] at lo
    omega
  have stencil : StencilBook.ScalarRoom (fun h i=>(p h i).middle.stencil):=by
    refine ⟨axes.oldHost,oldG,M,L.of_le (fun h i=>Nat.pow_le_pow_right (by decide) (rr h i).le),
      cal.dimension.bounded height,c D,1,?_⟩
    filter_upwards [widths] with h w
    intro i
    have ok:=w i
    have small:h/2≤1*h:=by simpa only [Nat.one_mul] using Nat.div_le_self h 2
    exact ⟨ok.layers.trans small,ok.cutoff.trans small,ok.readers.trans small,ok.planes.trans small,ok.gather.trans small⟩
  refine ⟨stencil,L,M,oldG.of_le (fun h i=>Nat.pow_le_pow_right (by decide) ((Nat.sub_le ..).trans (cuts h i).2)),
    (c 2).mul (cal.previousCap.bounded height),axes.oldHost,(cal.dimension.bounded height).of_le (fun h i=>(dims h i).le),
    oldG.of_le (fun _ _=>Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)),oldG,c (2^(GroupStage.depthBound D n f g)),
    field,original_root_law G board op t f g reset τ D drift B sites age size degree root previous nextM base old seed earlier next priced,
    ?_,?_,?_⟩
  · filter_upwards [priced] with h keys
    intro i
    let m:=(p h i).middle
    have paid:=keys i ((m.signedBits+m.signedBits)*2^m.rootDepth) (.inl (by
      change (m.signedBits+m.signedBits)*2^m.rootDepth ∈ (p h i).rootUnits
      simp [rootUnits,m]))
    change (m.signedBits+m.signedBits)*2^(root h i+k_ h)≤h/2
    change ((m.signedBits+m.signedBits)*2^(k_ h))*2^(root h i) ≤ h/2 at paid
    simpa only [pow_add,Nat.mul_comm (2^(root h i)) (2^(k_ h)),Nat.mul_assoc] using paid
  · filter_upwards [axes.halfMatrix] with h good
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
