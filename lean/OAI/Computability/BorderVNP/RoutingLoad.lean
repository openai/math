import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Round-robin routing on the complete team graph

In §8.3 of *An explicit VNP family requires superpolynomial border circuit size
over every field*, each unordered pair distributes its bits cyclically over
all teams except the two endpoints. Each physical block can be used with either
endpoint acting as a relay. Equation (8.2) bounds the sum of those two loads.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Routing

open Finset

variable {R : ℕ}

/-- Intermediate teams available for a transmission between two endpoints. -/
def pool (u w : Fin R) : Finset (Fin R) := (univ.erase u).erase w

/-- Removing the two distinct endpoints leaves exactly `R - 2` relays. -/
theorem pool_card {u w : Fin R} (h : u ≠ w) :
    (pool u w).card = R - 2 := by
  have hw : w ∈ (univ : Finset (Fin R)).erase u := by simp [h.symm]
  simp only [pool, card_erase_of_mem hw, card_erase_of_mem (mem_univ u), card_univ, Fintype.card_fin]
  omega

/-- Team used for transmission number `j` in a pair's list, in increasing
team-number order with both endpoints omitted. -/
def relay (hR : 2 < R) {u w : Fin R} (h : u ≠ w) (j : ℕ) : Fin R :=
  (pool u w).orderEmbOfFin (pool_card h) ⟨j % (R - 2), Nat.mod_lt _ (by omega)⟩

/-- Both endpoints compute the same relay from their copy of the ordered
transmission list. -/
theorem relay_swap (hR : 2 < R) {u w : Fin R} (h : u ≠ w) (j : ℕ) :
    relay hR h j = relay hR h.symm j := by
  have hp : pool u w = pool w u := by
    ext x
    simp [pool, and_comm]
  simp only [relay, orderEmbOfFin_apply]
  congr 1
  rw [hp]

/-- Every routed bit goes through a third team. -/
theorem relay_ne_endpoints (hR : 2 < R) {u w : Fin R} (h : u ≠ w) (j : ℕ) :
    relay hR h j ≠ u ∧ relay hR h j ≠ w := by
  have hm : relay hR h j ∈ pool u w := (pool u w).orderEmbOfFin_mem _ _
  simpa [pool, and_comm] using hm

/-- Ordinals of the bits from an endpoint pair passing through relay `v`. -/
def pairBits (hR : 2 < R) (u w v : Fin R) (width : ℕ) : Finset ℕ :=
  if h : u ≠ w then (range width).filter (fun j ↦ relay hR h j = v) else ∅

/-- How many of the bits from a given endpoint pair pass through `v`. -/
def pairLoad (hR : 2 < R) (u w v : Fin R) (width : ℕ) : ℕ :=
  (pairBits hR u w v width).card

/-- Each relay handles at most one bit per full round and one more in the
last, possibly incomplete round. -/
theorem pairLoad_le (hR : 2 < R) (u w v : Fin R) (width : ℕ) :
    pairLoad hR u w v width ≤ width / (R - 2) + 1 := by
  by_cases h : u ≠ w
  · rw [pairLoad, pairBits, dite_eq_left h]
    rw [← card_range (width / (R - 2) + 1)]
    apply card_le_card_of_injOn (fun j ↦ j / (R - 2))
    · intro j hj
      have hj' := mem_range.mp (mem_filter.mp hj).1
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hj'.le))
    · intro i hi j hj hij
      have he := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
      have hm := congrArg Fin.val (((pool u w).orderEmbOfFin (pool_card h)).injective he)
      change i % (R - 2) = j % (R - 2) at hm
      change i / (R - 2) = j / (R - 2) at hij
      calc
        i = i % (R - 2) + (R - 2) * (i / (R - 2)) := (Nat.mod_add_div ..).symm
        _ = j % (R - 2) + (R - 2) * (j / (R - 2)) := by rw [hm, hij]
        _ = j := Nat.mod_add_div ..
  · simp [pairLoad, pairBits, h]

/-- The width of the unordered demand list, indexed in increasing endpoint
order. Co-located transmissions use no physical link. -/
def demand (width : Fin R → Fin R → ℕ) (u w : Fin R) : ℕ :=
  if u = w then 0 else width (min u w) (max u w)

/-- Load on the block joining `u` and `v` due to transmissions for which `u`
is an endpoint and `v` is the relay. -/
def legLoad (hR : 2 < R) (width : Fin R → Fin R → ℕ) (u v : Fin R) : ℕ :=
  ∑ w, pairLoad hR u w v (demand width u w)

/-- In one direction on a block, the endpoint's total demand is divided by
the relay count, with at most one extra bit for each possible partner. -/
theorem legLoad_le (hR : 2 < R) (width : Fin R → Fin R → ℕ) (u v : Fin R) :
    legLoad hR width u v ≤ (∑ w, demand width u w) / (R - 2) + R := by
  have hsum : (∑ w, demand width u w / (R - 2)) ≤ (∑ w, demand width u w) / (R - 2) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < R - 2)).2
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun _ _ ↦ Nat.div_mul_le_self _ _
  calc
    legLoad hR width u v ≤ ∑ w, (demand width u w / (R - 2) + 1) :=
      sum_le_sum fun w _ ↦ pairLoad_le hR u w v _
    _ = (∑ w, demand width u w / (R - 2)) + R := by simp [sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_right hsum R

/-- Equation (8.2), with integer division and both uses of the same physical
block counted. `X` denotes the exterior communication budget of one team. -/
theorem blockLoad_le (hR : 2 < R) (width : Fin R → Fin R → ℕ) (X : ℕ)
    (budget : ∀ u, ∑ w, demand width u w ≤ X / 64) (u v : Fin R) :
    legLoad hR width u v + legLoad hR width v u ≤ 2 * (X / (64 * (R - 2)) + R) := by
  have dir (x y : Fin R) : legLoad hR width x y ≤ X / (64 * (R - 2)) + R := by
    rw [← Nat.div_div_eq_div_mul]
    exact (legLoad_le hR width x y).trans (Nat.add_le_add_right (Nat.div_le_div_right (budget x)) _)
  rw [two_mul]
  exact Nat.add_le_add (dir u v) (dir v u)

end Routing

end BorderVNP
end Computability
end OAI
