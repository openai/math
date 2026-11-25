import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Changing the grouped site to a basis of slices

The rows of a grouped tensor are its coordinate slices. Replacing these rows
by a basis of their span gives mutual restrictions by linear maps on the
grouped factor. The coordinate indexing the ungrouped factors can itself be
a product, and the maps below leave every such coordinate fixed.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

variable {K A B I : Type*} [Field K] [Fintype A] [Fintype I]

/-- The grouped-site coefficient maps in both directions between a tensor's
family of slices and a basis of their span. -/
theorem groupedSliceBasis_mutualRestriction (rows : A → B → K)
    (w : Module.Basis I K (Submodule.span K (Set.range rows))) :
    (∃ expand : A → I → K, ∀ a b,
      ∑ i, expand a i * (w i).val b = rows a b) ∧
    (∃ compress : I → A → K, ∀ i b,
      ∑ a, compress i a * rows a b = (w i).val b) := by
  classical
  let row (a : A) : Submodule.span K (Set.range rows) :=
    ⟨rows a, Submodule.subset_span (Set.mem_range_self a)⟩
  constructor
  · refine ⟨fun a => w.repr (row a), ?_⟩
    intro a b
    have h := congrArg (fun x : Submodule.span K (Set.range rows) => x.val b)
      (w.sum_repr (row a))
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, row] using h
  · have h (i : I) := (Submodule.mem_span_range_iff_exists_fun K).mp (w i).property
    choose compress hcompress using h
    refine ⟨compress, fun i b => ?_⟩
    simpa [Finset.sum_apply] using congrFun (hcompress i) b

end SpectralBooks
end LinearAlgebra
end OAI
