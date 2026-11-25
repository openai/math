import OAI.LinearAlgebra.SpectralBooks.CrossingShortening
import OAI.LinearAlgebra.SpectralBooks.ProfileSelectorCost
import OAI.LinearAlgebra.SpectralBooks.ProfileNetworkProduct

/-!
# Amplifying a fixed-format sum of crossing networks

Expanding a tensor power assigns one network to each word of summand indices. Concatenating
the wires of that word and multiplying its local tables realizes its summand. A common block
of copies amortizes the cost of rounding selector tags to an integral bit width.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Crossing

open scoped BigOperators Classical

noncomputable section

/-- An exact sum of networks with a common bound on their individual costs. -/
structure CrossingNetworkSum (F : Type*) [CommSemiring F] (D m A : ℕ) (budget : ℝ) where
  count : Fin A → ℕ
  wires : (a : Fin A) → Fin (count a) → Wire (AxisSite D)
  tables : (a : Fin A) → LocalTables (B := AxisLeg m) (wires a) F
  realizes : ∀ x, crossingTensor F D m x = ∑ a, network (wires a) (tables a) x
  cost_le : ∀ a, ∑ i, wireCost (fun p q => dist (axisPoint p) (axisPoint q)) (wires a i) ≤ budget

variable {F : Type*} [CommSemiring F] {A D m : ℕ} {budget : ℝ}

private def axisLegBlock {t : ℕ} (i : AxisSite D) (x : AxisLeg (m * t) i) (r : Fin t) :
    AxisLeg m i := match i with
  | none => ()
  | some _ => fun s => x (finProdFinEquiv (s, r))

private theorem crossingTensor_blocks (t : ℕ) (x : ∀ i : AxisSite D, AxisLeg (m * t) i) :
    crossingTensor F D (m * t) x =
      ∏ r : Fin t, crossingTensor F D m (fun i => axisLegBlock i (x i) r) := by
  exact crossingEntry_tensorPower F () (fun i => x (some (i, false))) (fun i => x (some (i, true)))

/-- A tensor power of an exact sum has one network for every word of summands. Its wires
are the concatenation of the chosen networks' wires and their costs add. -/
def CrossingNetworkSum.amplify (S : CrossingNetworkSum F D m A budget) (t : ℕ) :
    CrossingNetworkSum F D (t * m) (A ^ t) (t * budget) := by
  rw [Nat.mul_comm t m]
  let ord : (Fin t → Fin A) ≃ Fin (A ^ t) := Fintype.equivFinOfCardEq (by simp)
  let block := @axisLegBlock D m t
  have hprod (w : Fin t → Fin A) := exists_parallelNetwork
    (fun r => S.count (w r)) (fun r => S.wires (w r)) (fun r => S.tables (w r)) block
  choose c W T hentry hcost using hprod
  refine ⟨c ∘ ord.symm, W ∘' ord.symm, T ∘' ord.symm, ?_, ?_⟩
  · intro x
    rw [crossingTensor_blocks]
    simp_rw [S.realizes, Fintype.prod_sum]
    calc
      _ = ∑ w : Fin t → Fin A, network (W w) (T w) x :=
        Finset.sum_congr rfl fun w _ => (hentry w x).symm
      _ = _ := (ord.symm.sum_comp _).symm
  · intro a
    change ∑ i, wireCost _ (W (ord.symm a) i) ≤ _
    rw [hcost]
    simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ)
      (fun r _ => S.cost_le (ord.symm a r))

/-- Blocking a shortened crossing gives fixed binary tags and a positive relative saving,
including their broadcast from the origin to all endpoints. -/
theorem ShortenedCrossing.exists_profile_block (hs : ShortenedCrossing F D m) (hD : 0 < D)
    (hm : 0 < m) : ∃ (M A b : ℕ) (budget ν : ℝ),
      0 < M ∧ 0 < A ∧ 0 < ν ∧ ν < 1 ∧ budget + 2 * D * b ≤ (1 - ν) * 2 * D * M ∧
      Nonempty (Fin A ↪ (Fin b → Bool)) ∧ Nonempty (CrossingNetworkSum F D M A budget) := by
  obtain ⟨A, w, c, W, T, hA, hentry, hcost, hshort⟩ := hs
  let S : CrossingNetworkSum F D m A w := ⟨c, W, T, hentry, hcost⟩
  obtain ⟨t, b, ν, ht, hb, hν, hν', hbudget⟩ := exists_profile_selector_block hA hD hm hshort
  exact ⟨t * m, A ^ t, b, t * w, ν, Nat.mul_pos ht hm, pow_pos hA t, hν, hν', hbudget,
    ⟨profileSelectorTag hb⟩, ⟨S.amplify t⟩⟩

end
end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
