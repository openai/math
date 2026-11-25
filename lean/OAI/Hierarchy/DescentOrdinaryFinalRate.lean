import OAI.Hierarchy.DescentOrdinaryFinalChart
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Address bound for normalization of the resolved ordinary keys -/
namespace Hierarchy.DescentOrdinaryFinal.Chart
open DescentDatedAddressBook Filter
variable {ι : ℕ→Type*} (p : ∀ h,ι h→DescentOrdinaryFinal.Chart)
structure ScalarRoom : Prop where
  nodes : Bounded (fun h i=>(p h i).layout.nodes)
  args : Bounded (fun h i=>(p h i).layout.operands)
  blocks : Bounded (fun h i=>(p h i).layout.blocks)
  rows : Bounded (fun h i=>(p h i).rows)
  keyWidth : ∃ K : ℕ,∀ᶠ h in atTop,∀i,
    let B:=p h i
    (B.scalarWidth*B.inputs+B.scalarWidth)*B.layout.lanes≤K*h

theorem extent_rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0) :=by
  obtain ⟨K,hK⟩:=r.keyWidth
  have joined:=Bounded.pow_of_linear (K:=K) hK
  have small : Bounded (fun h i=>2^((p h i).scalarWidth*(p h i).layout.lanes)):=by
    apply joined.of_le
    intro h i
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_left ..))
  have inputBound : Bounded (fun h i=>(p h i).inputs) := by
    simpa only [inputs,keys] using (Bounded.const 3).add (r.nodes.mul r.args)
  have outputBound : Bounded (fun h i=>(p h i).outputs) := by
    simpa only [outputs] using (Bounded.const 7).mul r.args
  have cast:=(Bounded.const 4).mul ((Bounded.const 2).mul small)
  have law:=(inputBound.add outputBound).mul ((Bounded.const 2).mul joined)
  have scan:=(outputBound.mul r.blocks).mul r.rows
  have guard:=(r.rows.add (Bounded.const 1)).padded
  simpa only [endAddress,out,castEnd,castWords,tableWords,passes,Nat.zero_add] using
    (((cast.add law).add scan).add guard)
end Hierarchy.DescentOrdinaryFinal.Chart

end OAI
