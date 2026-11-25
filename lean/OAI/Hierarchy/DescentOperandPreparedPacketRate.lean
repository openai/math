import OAI.Hierarchy.DescentOperandPreparedPacketPhase
import OAI.Hierarchy.DescentResetStemProjectRate

namespace OAI
/-! # Address exponents for the two aligned original operand packets -/
namespace Hierarchy.DescentOperandRootPull.Pair
open Filter DescentDatedAddressBook DescentSIMDLookup ProtocolRAM
variable {ι : ℕ→Type*}

structure ScalarRoom (p : ∀h,ι h→Pair) : Prop where
  actors : Bounded (fun h i=>(p h i).actors)
  receivers : Bounded (fun h i=>(p h i).receivers)
  groups : Bounded (fun h i=>(p h i).groups)
  blocks : Bounded (fun h i=>(p h i).blocks)
  previous : Bounded (fun h i=>(p h i).beforeLanes)
  lanes : Bounded (fun h i=>(p h i).afterLanes)
  count : ∀f,Bounded (fun h i=>((p h i).stage 0 f).fields)
  input : ∀f,∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,((p h i).stage 0 f).width*(p h i).beforeLanes≤K*h
  output : ∀f,∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(((p h i).stage 0 f).width*(p h i).blocks)*(p h i).afterLanes≤K*h
  blocksPositive : ∀h i,0<(p h i).blocks

theorem stage_rate (p : ∀h,ι h→Pair) (s : ScalarRoom p) (f : Bool) :
    Bounded (fun h i=>((p h i).stage 0 f).endAddress) := by
  let L:=fun h (i : ι h)=>(p h i).stage 0 f
  have one:=Bounded.const (ι:=ι) 1
  have two:=Bounded.const (ι:=ι) 2
  have four:=Bounded.const (ι:=ι) 4
  have three:=Bounded.const (ι:=ι) 3
  have root:=DescentResetStemProject.rates (a:=fun h i=>(L h i).width) one s.actors s.groups s.blocks
    s.previous s.lanes (s.input f) (s.output f)
  have chunks_ : Bounded (fun h i=>chunks (p h i).groups (p h i).afterLanes) :=
    (s.groups.add s.lanes).of_le (fun h i=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have parents : Bounded (fun h i=>DescentResetStemKeyReindex.size (p h i).actors (p h i).receivers (p h i).groups (p h i).afterLanes) :=
    (((two.mul s.actors).add (four.mul (s.receivers.mul chunks_))).add three).of_le
      (fun h i=>DescentResetStemKeyReindex.size_le ..)
  obtain ⟨K,hl⟩:=s.output f
  have expBound : ∀ᶠ h:ℕ in atTop,∀i,DescentOperandFamilyBook.unit 1 (L h i).width*(p h i).afterLanes≤(2*K)*h := by
    filter_upwards [hl] with h upper
    intro i
    have grow:=Nat.mul_le_mul_right (p h i).afterLanes
      (Nat.le_mul_of_pos_right (L h i).width (s.blocksPositive h i))
    have small : (L h i).width*(p h i).afterLanes≤K*h:=grow.trans (upper i)
    unfold DescentOperandFamilyBook.unit
    rw [Nat.mul_one,Nat.add_mul,Nat.mul_assoc]
    omega
  have outputSize:=((one.add (s.count f)).mul (two.mul (Bounded.pow_of_linear expBound)))
  exact (root.add parents).add outputSize

theorem extent_rate (p : ∀h,ι h→Pair) (s : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0) := by
  have a:=stage_rate p s false
  have b:=stage_rate p s true
  apply (a.add b).of_le
  intro h i
  change ((p h i).stage ((p h i).stage 0 false).endAddress true).endAddress≤_
  rw [((p h i).stage ((p h i).stage 0 false).endAddress true).extent]
  rfl

end Hierarchy.DescentOperandRootPull.Pair

end OAI
