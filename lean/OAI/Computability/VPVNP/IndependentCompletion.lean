import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Extending a partial frame by a prescribed number of vectors -/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

/-- An independent tuple can be extended by any number of vectors up to its codimension. -/
theorem exists_independent_completion {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype ι] {v : ι → V}
    (hv : LinearIndependent K v) {k : ℕ} (hk : Fintype.card ι + k ≤ Module.finrank K V) :
    ∃ w : Fin k → V, LinearIndependent K (Sum.elim v w) := by
  let W := Submodule.span K (Set.range v)
  let f : ι → W := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hf : LinearIndependent K f := .of_comp W.subtype hv
  have hdim : Module.finrank K W = Fintype.card ι := finrank_span_eq_card hv
  have hq : k ≤ Module.finrank K (V ⧸ W) := by
    have := W.finrank_quotient_add_finrank
    omega
  obtain ⟨q, hq'⟩ := exists_linearIndependent_of_le_finrank hq
  choose w hw using fun i ↦ W.mkQ_surjective (q i)
  refine ⟨w, hf.sumElim_of_quotient w ?_⟩
  have he : Submodule.Quotient.mk (p := W) ∘ w = q := funext hw
  exact he.symm ▸ hq'

end Grassmann

end VPVNP
end Computability
end OAI
