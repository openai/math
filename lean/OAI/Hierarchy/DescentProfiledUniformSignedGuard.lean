import OAI.Hierarchy.DescentProfiledOrdinarySignedGuard
import OAI.Hierarchy.DescentProfiledOrdinaryUniformAxes

namespace OAI
/-! # Choosing the signed guard address exponent before the tail and the divisor -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale Chronology DescentDatedAddressBook Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)

private structure GuardSample (h : ℕ) where
  tailRate : ℕ
  budget : ℕ
  point : ProfiledOrdinaryOffer G f g board op t reset tailRate drift degreeMax budget h
  fits : RawLimits G board op t f g reset tailRate drift degreeMax budget h point

/-- All authentic ordinary offers share one address exponent.  Fixing the tail and the divisor
only determines when their public calendar measurements fit. -/
theorem uniform_signed_guard_excess : ∃K : ℕ,∀τ B : ℕ,∀ᶠ h : ℕ in atTop,
    ∀x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h,
      x.model.signedGuard x.stageFloor-x.model.signedEnd x.stageFloor≤2^(K*h) := by
  let I:=GuardSample G board op t f g reset drift degreeMax
  obtain ⟨K,bound⟩:=guard_from_axes G board op t f g reset drift degreeMax
    (ι:=I) (fun _ y=>y.tailRate) (fun _ y=>y.budget) (fun _ y=>y.point)
    ⟨4,Eventually.of_forall fun _ y=>y.fits.oldHost⟩
    ⟨4,Eventually.of_forall fun _ y=>y.fits.newHost⟩
    ⟨1,Eventually.of_forall fun _ y=>by simpa only [Nat.one_mul] using y.fits.newGroup⟩
    ⟨1,Eventually.of_forall fun _ y=>by simpa only [Nat.one_mul] using y.fits.blocks⟩
  refine ⟨K,fun τ B=>?_⟩
  filter_upwards [bound,raw_limits G board op t f g reset τ drift degreeMax B] with h cap actual
  intro x
  exact cap (⟨τ,B,x,actual x⟩ : I h)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
