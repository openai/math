import OAI.Hierarchy.DescentOriginalMoverUnits
import OAI.Hierarchy.DescentRetainedSevenFixedRate

namespace OAI
/-! # Public local dimensions of the reset operand transfer -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentRetainedHomeMover Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset D : ℕ)
local notation "E" => primitiveLocalExponent G board op t f g reset D

theorem original_seven_dimensions (τ drift B : ℕ) (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (bound : ℕ) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
    ∀sites age p degree e previous lanes nextM base old,p≤h→degree≤bound→
      let z:=originalSample G op t f g reset τ D drift J sites age p degree h e previous lanes nextM base old
      old.nodes≤z.sched.retainedNodes→ old.arguments≤z.sched.retainedArgumentsAt G drift→
        ∃lim : DescentRetainedSeven.Limits (scale J E),lim.chart=(z.output G board D f g op.C op.w).setup.seven:=by
  filter_upwards [original_fields G board op t f g reset τ D drift B positive branch bound,
    original_primitive_limits G board op t f g reset D τ drift B positive branch bound] with h active limits
  intro J sites age p degree e previous lanes nextM base old hp hd z prior arg
  let v:=z.output G board D f g op.C op.w
  have p₀:=limits sites age p degree e previous lanes nextM base old hp hd
  have coordinates:=active sites age p degree e previous lanes nextM base old hp hd
  have pos : localExponent G board op t f g reset D ≤ E :=
    (Nat.le_add_right (localExponent G board op t f g reset D) _).trans (Nat.le_add_right _ _)
  have d:z.sched.groupWidth z.k z.tail z.age+z.k≤ scale J E:=
    coordinates.dim.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ pos))
  have geom:v.setup.retained.CalendarPitch (z.sched.groupWidth z.k z.tail z.age) z.k h v.retainedUnit:=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨⟨v.setup.seven,?_,prior.trans p₀.nodes,arg.trans p₀.args,p₀.nodes,p₀.args,p₀.blocks,p₀.blocks,p₀.shapes⟩,rfl⟩
  change v.setup.retained.high + v.setup.retained.low ≤ scale J E
  rw [(DescentResetRetainedSetup.Layout.CalendarPitch.geometry _ geom).1]
  exact d

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
