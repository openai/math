import OAI.Hierarchy.DescentUniformSurvivorGeometry

namespace OAI
/-! The exponent of the five survivor allocations is chosen before the schedule parameters. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology DescentDatedAddressBook Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)

private structure SurvivorSample (h : ℕ) where
  tailRate : ℕ
  budget : ℕ
  point : ProfiledOrdinaryOffer G f g board op t reset tailRate drift degreeMax budget h
  admission : SignedAdmission G board op t f g reset drift degreeMax tailRate budget h point

theorem uniform_survivor :
    ∃ e : ℕ, ∀ τ B : ℕ, SignedStage.unitRate G t f g reset < B →
      ∀ᶠ h : ℕ in atTop, ∀ x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h,
        x.model.survivorWords ≤ 2^(e*h) := by
  let I := SurvivorSample G board op t f g reset drift degreeMax
  obtain ⟨e,bound⟩ := (material_and_survivor G board op t f g reset drift degreeMax (ι := I)
    (fun _ y => y.tailRate) (fun _ y => y.budget) (fun _ y => y.point) (fun _ y => y.admission)).2
  refine ⟨e,fun τ B slack => ?_⟩
  filter_upwards [bound,signed_admission G board op t f g reset drift degreeMax τ B slack] with h paid available
  exact fun x => paid (⟨τ,B,x,available x⟩ : I h)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
