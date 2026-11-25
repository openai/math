import OAI.Hierarchy.GraphWireClass
import OAI.Hierarchy.WireProductPrice
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI
/-! # Price of the graph coefficient tensor before grouping its edge ends -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators

variable {E : Type} [Fintype E] [Nonempty E] {F X : Type*} [Field F]

/-- Assigning a point to each edge end charges each edge its length times its width. -/
theorem equalityWireRaw_price [MetricSpace X] (P : SpectralPlacementPrices F X)
    (x : E × Bool → X) (q : ℕ) (hq : 0 < q) :
    P.price (equalityWireRaw E F q) x =
      ∑ e, dist (x (e,false)) (x (e,true)) * Real.logb 2 q :=
  WirePrice.wires P x (fun e => (e,false)) (fun e => (e,true)) q hq _ (ofRaw_equalityWireRaw E F q)

/-- For antipodal unit endpoints the wire product attains the sum of its leg widths. -/
theorem equalityWireRaw_price_antipodal [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : SpectralPlacementPrices F X) (x : E × Bool → X) (q : ℕ) (hq : 0 < q)
    (unit : ∀ e, ‖x (e,false)‖ = 1) (antipodal : ∀ e, x (e,true) = -x (e,false)) :
    P.price (equalityWireRaw E F q) x = ∑ _ : E × Bool, Real.logb 2 q := by
  have diameter (e : E) : dist (x (e,false)) (x (e,true)) = 2 := by
    rw [antipodal,dist_eq_norm,sub_neg_eq_add,← two_smul ℝ (x (e,false)),norm_smul,unit]
    norm_num
  rw [equalityWireRaw_price P x q hq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  simp only [diameter,Fintype.sum_bool,two_mul]


end Hierarchy

end OAI
