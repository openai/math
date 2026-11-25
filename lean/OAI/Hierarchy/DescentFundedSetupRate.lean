import OAI.Hierarchy.DescentFundedSetupLayout
import OAI.Hierarchy.DescentDatedOverlapAperture

namespace OAI
/-! # Address exponent for the paid-group remix and the receiving signed masks -/
namespace Hierarchy.DescentFundedCensus.Setup
open DescentDatedAddressBook DescentSIMDLookup DescentGLPacked.BankImage DescentGLNielsen DescentGLControlCode Filter
noncomputable section
variable {ι : ℕ→Type*} (s : ∀h,ι h→DescentFundedCensus.Setup)

structure ScalarRoom : Prop where
  host : Bounded (fun h i=>(s h i).hosts)
  group : Bounded (fun h i=>(s h i).oldGroups)
  blocks : Bounded (fun h i=>(s h i).blocks)
  old : Bounded (fun h i=>(s h i).oldLanes)
  gather : Bounded (fun h i=>(s h i).gatherLanes)
  width : ∃K:ℕ,∀ᶠ h : ℕ in atTop,∀i,let a:=s h i
    a.precision*a.oldLanes≤K*h ∧ (a.precision*a.blocks+a.precision)*a.gatherLanes≤K*h ∧
    (a.precision+a.precision)*2^a.low≤K*h ∧ (a.high+a.low)*(a.high+a.low)≤K*h ∧ a.flagWidth≤K*h

theorem rate (r : ScalarRoom s) : Bounded (fun h i=>(s h i).roof 0) := by
  obtain ⟨K,hk⟩:=r.width
  let c n:=Bounded.const (ι:=ι) n
  have strip : Bounded (fun h i=>(s h i).stripSpan) := Overlap.address_rate r.host r.group r.old r.gather
    ⟨K,hk.mono fun h z i=>(z i).1⟩
  have joins:=Bounded.pow_of_linear (K:=K) (hk.mono fun h z i=>(z i).2.1)
  have residual:=Bounded.pow_of_linear (K:=K) (hk.mono fun h z i=>(z i).2.2.2.2)
  have power : Bounded (ι:=ι) (fun h _=>2^(K*h)):=⟨K,Eventually.of_forall fun _ _=>le_rfl⟩
  have axisExp : Bounded (fun h i=>2^((s h i).high+(s h i).low)):=by
    apply Bounded.pow_of_linear (K:=K)
    filter_upwards [hk] with h hh
    intro i
    have key:=(hh i).2.2.2.1
    by_cases dim : (s h i).high+(s h i).low=0
    · simp [dim]
    · exact (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero dim)).trans key
  have dims : Bounded (fun h i=>(s h i).high+(s h i).low) :=axisExp.of_le fun _ _=>Nat.lt_two_pow_self.le
  have rows:=axisExp.of_le (y:=fun h i=>2^(s h i).high) fun _ _=>Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  have counter : Bounded (fun h i=>Count ((s h i).high+(s h i).low)) :=
    (((c 3).mul dims).mul dims).of_le fun _ _=>DescentGLNielsen.length_le _
  have matrix : Bounded (fun h i=>(s h i).matrix 0) :=
    (((c 0).add (r.blocks.mul strip)).add (r.blocks.mul ((c 2).mul joins)))
  have sized := r.host.mul rows
  have directory := ((((c 1).add counter).mul power).add counter).add (dims.mul rows)
  have safe := ((matrix.add ((c 4).mul (directory.add (c 1)))).add
    ((c 2).mul (sized.add (c 1)))).add counter
  have rhs:=safe.add ((((c 7).mul counter).add (c 1)).mul (((c 2).mul (sized.add (c 1))).add power))
  obtain ⟨A,ea⟩:=rhs
  have signed : Bounded (fun h i=>(s h i).signedEnd 0):=by
    refine ⟨A,?_⟩
    filter_upwards [ea,hk] with h estimate st
    intro i
    let v:=s h i
    have half : 2*(K*h)/2=K*h:=by omega
    have cost:=Dated.paid_extent (v.matrix 0) (1*v.hosts) v.high v.low v.precision (2*(K*h))
      (by simpa only [half] using (st i).2.2.1) (by simpa only [half] using (st i).2.2.2.1)
    exact cost.trans (by simpa only [half,Nat.one_mul] using estimate i)
  exact signed.add residual

end
end Hierarchy.DescentFundedCensus.Setup

end OAI
