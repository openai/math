import OAI.Hierarchy.PrimeFlats
import OAI.Hierarchy.ValiantSeparation

namespace OAI
namespace Hierarchy
namespace Valiant

/-- Each consecutive pair of arithmetic classes is strictly separated over the same field. -/
theorem strict_inclusions (F : Type*) [Field F] :
    VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F := by
  obtain ⟨formula, program, _⟩ := separations_of_prime_flats prime_flats F
  exact ⟨formula, by simpa only [vp_eq] using program, vp_ssubset_vnp F⟩

end Valiant
end Hierarchy
end OAI
