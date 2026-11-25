import OAI.LinearAlgebra.SpectralBooks.PowerSpan
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # A polynomial dimension bound for the span of coordinate powers

Each tensor power is constant on words with the same histogram. Pullback
from the space of functions of the histogram consequently bounds the
dimension of the power span over any field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The powers of a set of tensors span a space of dimension polynomial in
the degree; the number of coordinate indices is fixed. -/
theorem coordinatePower_span_finrank_le (n : ℕ) (S : Set (ι → K)) :
    Module.finrank K (Submodule.span K (coordinatePower n '' S)) ≤ (n+1) ^ Fintype.card ι := by
  classical
  let W := Fin n → ι
  let H := ι → Fin (n+1)
  let hist (w : W) (i : ι) : Fin (n+1) := ⟨(Finset.univ.filter (w · = i)).card,
    Nat.lt_succ_of_le (by simpa using Finset.card_filter_le Finset.univ (w · = i))⟩
  let pull : (H → K) →ₗ[K] W → K :=
    { toFun := fun f w ↦ f (hist w)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hle : Submodule.span K (coordinatePower n '' S) ≤ LinearMap.range pull := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, rfl⟩
    refine ⟨fun a ↦ ∏ i, x i ^ (a i : ℕ), ?_⟩
    ext w
    simpa only [pull, hist, coordinatePower, LinearMap.coe_mk, AddHom.coe_mk, Finset.prod_const]
      using Finset.prod_fiberwise' Finset.univ w x
  calc
    _ ≤ Module.finrank K (LinearMap.range pull) := Submodule.finrank_mono hle
    _ ≤ Module.finrank K (H → K) := pull.finrank_range_le
    _ = _ := by simp [H]

/-- One bounded family of tensors from the original set spans all of its
coordinate powers of a prescribed degree. -/
theorem exists_finset_coordinatePower_span (n : ℕ) (S : Set (ι → K)) :
    ∃ s : Finset (ι → K), (s : Set (ι → K)) ⊆ S ∧ s.card ≤ (n+1) ^ Fintype.card ι ∧
      Submodule.span K (coordinatePower n '' (s : Set (ι → K))) =
        Submodule.span K (coordinatePower n '' S) := by
  classical
  obtain ⟨v, hv, hsp, _⟩ := Submodule.exists_fun_fin_finrank_span_eq K (coordinatePower n '' S)
  choose f hf heq using hv
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · rintro _ hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hf i
  · apply (Finset.card_image_le).trans
    simpa using coordinatePower_span_finrank_le n S
  · refine Eq.trans ?_ hsp
    congr 1
    ext p
    simp [heq]

end SpectralBooks
end LinearAlgebra
end OAI
