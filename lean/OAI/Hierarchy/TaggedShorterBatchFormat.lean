import OAI.Hierarchy.CorrectionFrame
import OAI.Hierarchy.TaggedData

namespace OAI
/-! # Numbering the single amplified product at each shorter type -/

noncomputable section
namespace Hierarchy.TaggedShorterBatchFormat
open scoped BigOperators Classical

/-- Both calls at each physical module belong to the same homogeneous family. -/
def copy (M : ℕ) : Fin M × Bool ≃ Fin (M*2) :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

/-- The numbered hole has exactly the row-major data layout of the amplified
tensor on all installed calls. -/
def pin (M p : ℕ) : (Fin M × (Bool × Fin p)) ≃ Fin ((M*2)*p) :=
  (Equiv.prodAssoc (Fin M) Bool (Fin p)).symm |>.trans
    ((Equiv.prodCongr (copy M) (Equiv.refl _)).trans finProdFinEquiv)

theorem product_eq {F : Type*} [CommMonoid F] {M p : ℕ} (f : (Fin p → Bool) → F)
    (x : Fin ((M*2)*p) → Bool) :
    (∏ i : Fin M, f (fun j => x (pin M p (i,false,j))) * f (fun j => x (pin M p (i,true,j)))) =
      CorrectionFrame.dataProduct (M*2) f x := by
  unfold CorrectionFrame.dataProduct
  rw [← (copy M).prod_comp (fun i : Fin (M*2) => f (fun j => x (finProdFinEquiv (i,j))))]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.prod_bool,mul_comm]
  rfl

theorem slots (M h : ℕ) : (M*2)*2^h = 2*(M*2^h) := by ring

end Hierarchy.TaggedShorterBatchFormat

end
end OAI
