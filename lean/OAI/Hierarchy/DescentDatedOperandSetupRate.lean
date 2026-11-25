import OAI.Hierarchy.DescentDatedRetainedSevenRate
import OAI.Hierarchy.DescentOperandPreparedPacketRate
import OAI.Hierarchy.DescentResetOperandSetupChart
import OAI.Hierarchy.DescentDatedRetainedSetupRate
import OAI.Hierarchy.DescentDatedRetainedPlacementRate
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Word-address bound for the physical reset-operand setup -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentDatedAddressBook Filter
noncomputable section
variable {ι : ℕ→Type*} (p : ∀h,ι h→DescentResetOperandSetup.Chart)

structure ScalarRoom : Prop where
  publicWidth : ∃A:ℕ,∀ᶠ h in atTop,∀i,(p h i).publicCasts.bound*(p h i).publicCasts.lanes≤A*h
  packets : DescentOperandRootPull.Pair.ScalarRoom (fun h i=>(p h i).packets)
  old : DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>(p h i).retained)
  selected : DescentRetainedControl.Layout.ScalarRoom (fun h i=>(p h i).seven.control)
  placed : DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(p h i).placement)
    (fun h i=>(p h i).retainedFields)
  panels : DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(p h i).placement)
    (fun h i=>(p h i).signedFields)
  «fields» : Bounded (fun h i=>(p h i).inputs)
  members : Bounded (fun h i=>(p h i).members)
  fallback : Bounded (fun h i=>(p h i).fallbackInputs)
  width : ∃K : ℕ,∀ᶠ h:ℕ in atTop,∀i,let C:=p h i;
    C.sourceWidth*C.lanes≤K*h ∧ (C.fieldBits*C.inputs+C.fieldBits)*C.lanes≤K*h ∧
    (C.fieldBits+2)*C.lanes≤K*h ∧ (C.rotorBits*4+C.rotorBits)*C.lanes≤K*h ∧
    (C.fallbackBits*C.fallbackInputs+C.fallbackBits)*C.lanes≤K*h

theorem rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0) :=by
  have prior : Bounded (fun h i=>(p h i).placed 0):=by
    apply ((DescentRetainedSeven.Chart.extent_rate _ r.old r.selected r.placed).add
      (DescentResetRetainedPlacement.Chart.extent_rate _ _ r.panels)).of_le
    intro h i
    exact ((p h i).placement.affine _ _).le
  have packed : Bounded (fun h i=>(p h i).packetEnd 0) := by
    apply (prior.add (DescentOperandRootPull.Pair.extent_rate _ r.packets)).of_le
    intro h i
    exact le_of_eq ((p h i).packets.extent ((p h i).placed 0))
  have publicCast:=(DescentOperandPublicCasts.Plan.rate (fun h i=>(p h i).publicCasts) r.publicWidth).1
  have widened : Bounded (fun h i=>(p h i).publicEnd 0):=by
    simpa only [publicEnd,DescentOperandPublicCasts.Plan.endAddress,Nat.zero_add] using packed.add publicCast
  obtain ⟨K,limit⟩:=r.width
  have widths:=Bounded.pow_of_linear (K:=K) (limit.mono fun h hh i=>(hh i).1)
  have lookup:=Bounded.pow_of_linear (K:=K) (limit.mono fun h hh i=>(hh i).2.1)
  have part:=Bounded.pow_of_linear (K:=K) (limit.mono fun h hh i=>(hh i).2.2.1)
  have rotor:=Bounded.pow_of_linear (K:=K) (limit.mono fun h hh i=>(hh i).2.2.2.1)
  have other:=Bounded.pow_of_linear (K:=K) (limit.mono fun h hh i=>(hh i).2.2.2.2)
  have cast:=r.fields.mul ((Bounded.const 2).mul widths)
  have qs:=(r.fields.add (Bounded.const 1)).mul ((Bounded.const 2).mul lookup)
  have cs:=(r.fields.add (Bounded.const 2)).mul ((Bounded.const 2).mul lookup)
  have cuts:=(Bounded.const 10).mul part
  have n7:=(Bounded.const 7).mul r.members
  have rq:=((Bounded.const 4).add r.members).mul ((Bounded.const 2).mul rotor)
  have rf:=((Bounded.const 4).add n7).mul ((Bounded.const 2).mul rotor)
  have fq:=(r.fallback.add r.members).mul ((Bounded.const 2).mul other)
  have ff:=(r.fallback.add n7).mul ((Bounded.const 2).mul other)
  exact ((((((((widened.add cast).add qs).add cs).add cuts).add rq).add rf).add fq).add ff)

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
