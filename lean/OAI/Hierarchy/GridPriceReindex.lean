import OAI.Hierarchy.CorrectionProducts
import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.ShortenPrice

namespace OAI
/-! # Price of a relabelled external bit bank -/

noncomputable section
namespace Hierarchy.GridLens
open LinearAlgebra.SpectralBooks SiteTensor CorrectionProducts

private def singletonFiber {I J : Type} (e : I ≃ J) (j : J) :
    Bool ≃ ({i : I // e i = j} → Bool) where
  toFun b _ := b
  invFun v := v ⟨e.symm j,e.apply_symm_apply j⟩
  left_inv _ := rfl
  right_inv v := by
    funext i
    exact congrArg v (Subtype.ext (e.injective ((e.apply_symm_apply j).trans i.property.symm)))

/-- A bijection of port labels preserves the price at arbitrary positions,
including repeated and unoccupied sites. -/
theorem raw_price_reindex {I J : Type} [Fintype I] [Fintype J]
    {F M : Type*} [Field F] [MetricSpace M] [Nonempty M]
    (Q : SpectralPlacementPrices F M) (e : I ≃ J) (f : (I → Bool) → F) (x : J → M) :
    Q.price (raw (fun v : J → Bool => f (v ∘ e))) x = Q.price (raw f) (x ∘ e) := by
  rw [Q.group (raw f) e x]
  rcases isEmpty_or_nonempty J with h | h
  · let := h
    have collapsed : x = fun _ => Classical.arbitrary M := funext fun j => isEmptyElim j
    rw [collapsed,Q.collapsed,Q.collapsed]
  · let := h
    have equiv : (raw (fun v : J → Bool => f (v ∘ e))).Equivalent ((raw f).group e) := by
      exact Raw.reindex_equivalent (singletonFiber e) (fun _ => rfl)
    exact le_antisymm (Q.placed_mono x equiv.1) (Q.placed_mono x equiv.2)

end Hierarchy.GridLens

end
end OAI
