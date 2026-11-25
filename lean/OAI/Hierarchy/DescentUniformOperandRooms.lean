import OAI.Hierarchy.DescentProfiledOrdinaryBookRooms
import OAI.Hierarchy.DescentProfiledOrdinaryUniformAxes

namespace OAI
/-! Uniform address bounds for registered ordinary operand books use the same family of
physical layouts across all choices of the logarithmic divisor and calendar tail. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open Filter
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "exp_" => operandExponent G (stageNumbers G t 0 f g reset 0 0)
local notation "loc_" => OrdinaryBooks.primitiveLocalRate G t f g reset
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))

structure OperandLimits (h : ℕ) (x : idx h) : Prop where
  hosts : x.model.vector.hosts≤2^(4*h)
  lows : x.model.vector.lows≤2^((2*loc_)*h)
  nodes : x.model.resolver.nodes≤2^((2*loc_)*h)
  args : x.model.vector.operands≤2^((exp_+1)*h)
  blocks : x.model.vector.radix≤2^h
  groups : x.model.vector.groups≤2^h
  pitch : x.model.vector.lanes≤h

structure OperandSample (h : ℕ) where
  tailRate : ℕ
  budget : ℕ
  point : ProfiledOrdinaryOffer G f g board op t reset tailRate drift degreeMax budget h
  limits : OperandLimits G board op t f g reset tailRate drift degreeMax budget h point

theorem operand_sample_limits (den : 0<B) :
    ∀ᶠ h : ℕ in atTop, ∀ x : idx h, OperandLimits G board op t f g reset τ drift degreeMax B h x := by
  filter_upwards [raw_limits G board op t f g reset τ drift degreeMax B,
    OrdinaryBooks.primitive_date_local G op t f g reset τ B drift degreeMax den,
    eventually_ge_atTop (drift+1)] with h raw localBounds driftBound
  intro x
  have level : J_ h≤h := (Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have bound := localBounds x.slot.sites x.slot.age x.slot.p x.slot.degree
    (x.slot.menu.seats x.slot.age) x.slot.position.ports x.slot.grainLimit x.slot.degreeLimit
    (previous_nodes ..) x.firstWidth
  have version : scale (J_ h) loc_ ≤ 2^((2*loc_)*h) := by
    apply Nat.pow_le_pow_right (by decide)
    have height : J_ h + 1 ≤ 2*h := by omega
    calc
      _ ≤ loc_ * (2*h) := Nat.mul_le_mul_left _ height
      _ = _ := by ring
  refine ⟨?_,bound.2.2.2.2.2.2.trans version,bound.2.2.2.1.trans version,?_,
    (raw x).blocks,(raw x).newGroup,(pitch G board op t f g reset τ drift degreeMax B h x).1⟩
  · exact Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow (raw x).oldHost)
  · let S := S_ h x
    have original : x.model.vector.operands ≤ S.retainedArgumentsAt G drift :=
      max_le x.slot.geometry.room.args le_rfl
    apply original.trans
    change (drift+1)*(2^(J_ h))^exp_ ≤ _
    rw [←pow_mul]
    have fixed : drift+1≤2^h := driftBound.trans (Nat.lt_two_pow_self (n:=h)).le
    have multiplicity : 2^((J_ h)*exp_) ≤ 2^(h*exp_) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ level)
    calc
      _ ≤ 2^h*2^(h*exp_) := Nat.mul_le_mul fixed multiplicity
      _ = _ := by rw [←pow_add];congr 1;ring

namespace OperandSample

theorem rooms : PhysicalOrdinary.OperandRooms
    (fun h (y : OperandSample G board op t f g reset drift degreeMax h)=>y.point.model) := by
  apply PhysicalOrdinary.operand_rooms
  · exact Eventually.of_forall fun _ y=>y.point.prices
  · exact fun _ y=>y.point.base.registered_geometry y.point.slot.position.ports y.point.stageFloor
  · exact fun _ y=>(y.point.base.registered_node_chart y.point.slot.position.ports y.point.stageFloor).2
  · exact fun _ _=>rfl
  · exact ⟨4,Eventually.of_forall fun _ y=>y.limits.hosts⟩
  · exact ⟨_,Eventually.of_forall fun _ y=>y.limits.lows⟩
  · exact ⟨_,Eventually.of_forall fun _ y=>y.limits.nodes⟩
  · exact ⟨_,Eventually.of_forall fun _ y=>y.limits.args⟩
  · exact ⟨1,Eventually.of_forall fun _ y=>by simpa only [one_mul] using y.limits.blocks⟩
  · exact ⟨1,Eventually.of_forall fun _ y=>by simpa only [one_mul] using y.limits.groups⟩
  · exact ⟨1,Eventually.of_forall fun h y=>by simpa only [one_mul] using y.limits.pitch.trans (Nat.lt_two_pow_self (n:=h)).le⟩

end OperandSample

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
