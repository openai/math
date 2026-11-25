import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace OAI
/-! # Forward root sums and the available balance in a selected slot -/

namespace Hierarchy.GridChosenReceiver
open scoped BigOperators

/-- Regroup a flat cost per root, a native root cost, and the cost per saved pin. -/
theorem terminal_root_sum (n perRoot : ℕ) (rootCost len : ℕ → ℕ) :
    (∑ i : Fin n, (7224 + rootCost i.val + (perRoot + 22 * len i.val))) =
      7224*n + perRoot*n + (∑ i ∈ Finset.range n,rootCost i) + 22*(∑ i ∈ Finset.range n,len i) := by
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,
    ←Finset.mul_sum,Fin.sum_univ_eq_sum_range rootCost n,Fin.sum_univ_eq_sum_range len n]; ring

/-- The native writer's three headers and fixed-size cursor tail add at most 4226
steps after the map loop has been charged to forward root order. -/
theorem writer_headers {front maps empty perRoot n roots pins cursor : ℕ}
    (mapped : front+maps = empty+4+perRoot*n+roots+22*pins) (small : cursor≤100) :
    13+(front+(maps+(4096+((13+7224*n)+cursor)))) ≤
      (4226+empty)+(7224*n+perRoot*n+roots+22*pins) := by omega

/-- Dividing each S43 price into two paid pieces and its leftover works for an
empty root list and for nonuniform prices. -/
theorem selected_price_sum {n : ℕ} (price visit gather : Fin n → ℕ)
    (funded : ∀ i,visit i+gather i≤price i) :
    (∑ i,visit i)+(∑ i,gather i)+(∑ i,(price i-(visit i+gather i)))=∑ i,price i := by
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _=>Nat.add_sub_of_le (funded i)

end Hierarchy.GridChosenReceiver

end OAI
