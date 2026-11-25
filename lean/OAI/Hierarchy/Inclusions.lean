import OAI.Hierarchy.Classes
import OAI.Hierarchy.FormulaToABP
import OAI.Hierarchy.ABPCircuit
import OAI.Hierarchy.WitnessSum

namespace OAI
/-! # The inclusions of formal arithmetic complexity classes -/

namespace Hierarchy

/-- The simulations and the empty Boolean witness work over every field. -/
theorem inclusions (F : Type*) [Field F] :
    VF F ⊆ VBP F ∧ VBP F ⊆ VP F ∧ VP F ⊆ VNP F :=
  ⟨fun _ h => isVBP_of_isVF h, fun _ h => IsVBP.isVP h, fun _ h => isVNP_of_isVP h⟩

/-- The previously established VP versus VNP separation, in witness form. -/
def CircuitSeparation (F : Type*) [Field F] : Prop := ∃ p ∈ VNP F, p ∉ VP F

theorem strict_inclusions_of_witnesses (F : Type*) [Field F]
    (path : ∃ f ∈ VBP F, f ∉ VF F) (tree : ∃ f ∈ VP F, f ∉ VBP F)
    (circuit : CircuitSeparation F) :
    VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F := by
  obtain ⟨vf, abp, vp⟩ := inclusions F
  exact ⟨Set.ssubset_iff_exists.mpr ⟨vf, path⟩, Set.ssubset_iff_exists.mpr ⟨abp, tree⟩,
    Set.ssubset_iff_exists.mpr ⟨vp, circuit⟩⟩

end Hierarchy

end OAI
