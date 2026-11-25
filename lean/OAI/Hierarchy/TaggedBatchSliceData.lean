import OAI.Hierarchy.TaggedSliceData
import OAI.Hierarchy.CorrectionFrame

namespace OAI
/-! # Product identities for payload slices of independent tagged records -/

noncomputable section
namespace Hierarchy.Tagged.Slices
open scoped Classical BigOperators
open CorrectionFrame

variable {F : Type*} [Field F] {h w m : ℕ} (s : ℕ)
  (v : Fin m → ℕ) (total : ∑ i, v i = w)

def batchPin (i : Fin m) : Fin (s * pins h (v i)) → Fin (s * pins h w) :=
  finProdFinEquiv ∘ Prod.map id (pin v total i) ∘ finProdFinEquiv.symm

theorem batch_coeff [Nonempty (Fin m)] (x : Fin (s*pins h w) → Bool) :
    (∏ i, dataProduct s (coeff F h (v i)) (x ∘ batchPin s v total i)) =
      dataProduct s (coeff F h w) x := by
  simp only [dataProduct, Function.comp_apply, batchPin, Equiv.symm_apply_apply,
    Prod.map_apply, id_eq]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro l _
  exact coefficient v total (fun j => x (finProdFinEquiv (l,j)))

end Hierarchy.Tagged.Slices

end
end OAI
