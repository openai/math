import OAI.Computability.BorderVNP.PackedInheritedWorkWords
import OAI.Computability.BorderVNP.ShortenPublicParallelNames

/-! # Concatenating child work rows at a normalized sewing node -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Shortening.PublicParallel ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {σ : Type*} [Fintype σ] {w : ℕ}
variable {fan V : ℕ}

/-- Concatenate the site words at the input of the next normalized stage.
The preceding frame has already shared all child computations. -/
noncomputable def parallelRows (children : Frame σ (Fin fan × Fin V × Fin w)) : Frame σ (Fin (fan*V) × Fin w) :=
  children.select fun z => let i := finProdFinEquiv.symm z.1; (i.1,i.2,z.2)

/-- Holes in the parallel row numbering come from the corresponding child
rectangle. All other entries retain the exact previous extent. -/
theorem parallel_covers {X : Fin fan → Type*} (names : ∀ i, X i ↪ Fin V) (amount : ∀ i, X i → ℕ)
    (children : Frame σ (Fin fan × Fin V × Fin w)) (x : σ → Bool)
    (h : ∀ i, Covers (names i) (amount i) (children.select fun z => (i,z)) x) :
    Covers (parallelName names) (fun z => amount z.1 z.2) (parallelRows children) x := by
  have atRow (i : Fin fan) (r : Fin V) (j : Fin w) :
      (parallelRows children).eval x (flat i r,j) = children.eval x (i,r,j) := by
    simp only [parallelRows,Frame.select_eval,unflat_flat]
  constructor
  · rintro ⟨i,v⟩
    change value (fun j => (parallelRows children).eval x (flat i (names i v),j)) = amount i v
    simpa only [atRow,Frame.select_eval] using (h i).live v
  · intro i hi
    obtain ⟨⟨a,r⟩,rfl⟩ := finProdFinEquiv.surjective i
    have hr : r ∉ Set.range (names a) := fun he => hi ((parallelName_mem names a r).mpr he)
    change value (fun j => (parallelRows children).eval x (flat a r,j)) = 0
    simpa only [atRow,Frame.select_eval] using (h a).hole r hr

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
