import OAI.Hierarchy.DescentDatedRetainedPlacementRate

namespace OAI
/-! # The genuine prior-root and local-span inputs of the native primitive checkpoint -/
namespace Hierarchy.DescentPrimitiveBirth
open DescentDatedAddressBook DescentSIMDLookup Filter
noncomputable section
structure Layout where
  placement : DescentResetRetainedPlacement.Chart
  residual : ℕ
  rotorBits : ℕ
  nodes : ℕ
  arguments : ℕ
  rootBits : ℕ
  stop : ℕ
  sourceLanes : ℕ
  classBits : ℕ
  paidBits : ℕ
  spanBits : ℕ
namespace Layout
variable (z : Layout)
def roots :=2*(2^z.residual*2^z.rotorBits)
def batch : DescentResetRetainedPlacement.Batch :=⟨z.roots*z.nodes,z.rootBits,z.sourceLanes⟩
def liftBase (base : ℕ) :=base+z.nodes*(2*2^((z.rootBits*z.stop)*z.sourceLanes))
def lifted (base : ℕ) :=z.placement.endAddress z.batch (z.liftBase base)
def gates :=z.nodes+z.arguments+z.roots+2
def aperture :=max (z.classBits+z.paidBits) (max (z.spanBits+z.spanBits) (max (z.classBits+z.rootBits) (z.classBits+1)))
def endAddress (base : ℕ) :=z.lifted base+z.gates*(2*2^(z.aperture*z.placement.lanes))
theorem translate (base : ℕ) : z.endAddress base=base+z.endAddress 0:=by
  unfold endAddress lifted
  rw [z.placement.affine z.batch (z.liftBase base), z.placement.affine z.batch (z.liftBase 0)]
  simp only [liftBase, Nat.zero_add, Nat.add_assoc]

variable {ι : ℕ→Type*} (v : ∀h,ι h→Layout)
structure ScalarRoom : Prop where
  placement : DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(v h i).placement) (fun h i=>(v h i).batch)
  nodes : Bounded (fun h i=>(v h i).nodes)
  arguments : Bounded (fun h i=>(v h i).arguments)
  roots : Bounded (fun h i=>(v h i).roots)
  raw : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let z:=v h i;z.rootBits*z.stop*z.sourceLanes≤K*h
  words : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let z:=v h i;z.aperture*z.placement.lanes≤K*h

theorem rate (r : ScalarRoom v) : Bounded (fun h i=>(v h i).endAddress 0):=by
  obtain ⟨J,j⟩:=r.raw
  obtain ⟨K,k⟩:=r.words
  have d:=r.nodes.mul ((Bounded.const 2).mul (Bounded.pow_of_linear (K:=J) j))
  have p:=DescentResetRetainedPlacement.Chart.extent_rate _ _ r.placement
  have n:=((r.nodes.add r.arguments).add r.roots).add (Bounded.const 2)
  have lut:=n.mul ((Bounded.const 2).mul (Bounded.pow_of_linear (K:=K) k))
  apply ((d.add p).add lut).of_le
  intro h i
  rw [endAddress,lifted,(v h i).placement.affine (v h i).batch]
  simp [liftBase,gates]
end Layout
end
end Hierarchy.DescentPrimitiveBirth

end OAI
