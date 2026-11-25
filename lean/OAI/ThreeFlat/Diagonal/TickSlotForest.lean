import OAI.ThreeFlat.BitNetwork.OrderedGlue
import OAI.ThreeFlat.RAM.HistoryFactorLibrary
import OAI.ThreeFlat.RAM.HistoryFactorPadding

namespace OAI
/-! # A single weighted contraction for every cell assigned to a physical slot -/

namespace ThreeFlat.Diagonal.TickSlotForest

open BitNetwork.Ordered RAM.HistoryFactors
open scoped BigOperators
variable {F : Type*} {p n : ℕ}

def network (N : Fin n → BitNetwork F p) : BitNetwork F p :=
  glue N (fun _ i => (BitSource.pin i : BitSource 0 p))

@[simp] theorem cells (N : Fin n → BitNetwork F p) : (network N).cells = ∑ i, (N i).cells := rfl

@[simp] theorem internal (N : Fin n → BitNetwork F p) :
    (network N).internal = ∑ i, (N i).internal := by simp [network,glue]

/-- Every component receives the same physically mounted complete pin vector.
Disjoint internal variables give exactly the product, including the empty slot. -/
theorem eval [CommSemiring F] (N : Fin n → BitNetwork F p) (pin : Fin p → Bool) :
    (network N).eval pin = ∏ i, (N i).eval pin := by
  classical
  rw [network,glue_eval]
  simp [BitSource.read]

/-- Existing table IDs survive the copy to the slot stream. The number of
distinct table values and their eight entries are independent of the number
of cells selected by the owner scan. -/
def library (N : Fin n → BitNetwork F p) (count : ℕ)
    (table : Fin count → (Fin 3 → Bool) → F)
    (ids : (i : Fin n) → Fin (N i).cells → Fin count)
    (correct : ∀ i j, (N i).table j = table (ids i j)) : Library (network N) where
  count := count
  table := table
  id i := let c : Row N := finSigmaFinEquiv.symm i
          ids c.1 c.2
  correct i := by
    let c : Row N := finSigmaFinEquiv.symm i
    exact correct c.1 c.2

theorem padding_fits (N : Fin n → BitNetwork F p) (m : ℕ)
    (weight : (∑ i, 10000*((N i).cells+(N i).internal)) ≤ m/4) :
    (network N).internal ≤ m/40000 ∧
      (network N).cells+(m/40000-(network N).internal) ≤ 2*(m/40000) := by
  have h : 10000*((∑ i, (N i).cells)+(∑ i, (N i).internal)) ≤ m/4 := by
    simpa only [← Finset.mul_sum,Finset.sum_add_distrib] using weight
  rw [cells,internal]
  have h' : (∑ i, (N i).cells)+(∑ i, (N i).internal) ≤ m/40000 := by omega
  omega

end ThreeFlat.Diagonal.TickSlotForest

end OAI
