import OAI.Computability.BorderVNP.CubeLabelDirectoryProgram

/-! # Sparse end-to-end cost of constructing and traversing the label directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA.LabelTrial Finset
open scoped BigOperators

/-- Adding a live oriented cable increases the degree only at its two endpoints. -/
theorem Cable.prepend_length (e : Cable) (c : ℕ) (xs : List Incident) :
    (e.prepend c xs).length ≤ xs.length + (if c=e.src then 1 else 0) + (if c=e.dst then 1 else 0) := by
  unfold Cable.prepend
  split_ifs <;> (try simp only [List.length_cons]) <;> omega

/-- The total number of linked visits across the cells is at most twice the number
of physical cable descriptors, even with parallel cables and absorbed rows. -/
theorem incidence_count_le (rows : ℕ → Cable) (cells n : ℕ) :
    (∑ c ∈ range cells, (incidents rows c n).length) ≤ 2*n := by
  induction n with
  | zero => simp [incidents]
  | succ i ih =>
    have h := sum_le_sum (s := range cells) (fun c _ => (rows i).prepend_length c (incidents rows c i))
    change (∑ c ∈ range cells, ((rows i).prepend c (incidents rows c i)).length) ≤ _
    apply h.trans
    rw [sum_add_distrib,sum_add_distrib]
    simp only [sum_ite_eq',Finset.mem_range]
    split_ifs <;> omega

/-- Total cost of the fixed initializer followed by all candidate and commit passes. -/
def directoryTicks (l : Layout) (z : ℕ) (m : ℕ → ℕ) :=
  initTicks l + assignmentTicks RoutingISA.LabelTrial.setup.slots z l.cells
    (fun c => (directoryRows l m c).length)

/-- The complete machine is linear in the actual cell and descriptor counts and
uses a cubic factor in the number of labels. -/
theorem directoryTicks_le (l : Layout) (m : ℕ → ℕ) (z : ℕ) (hz : l.labels = z+1) :
    directoryTicks l z m ≤ 600*(1+l.cells+l.cableCount+l.deliveryCount)*(l.labels+1)^3 := by
  let n := 1+l.cells+l.cableCount+l.deliveryCount
  let k := (l.labels+1)^3
  have pos : 0 < n := by dsimp [n]; omega
  have one : 0 < k := by dsimp [k]; positivity
  have sq : l.labels^2 ≤ k := by
    dsimp [k]
    nlinarith only [Nat.zero_le (l.labels^3), Nat.zero_le (l.labels^2), Nat.zero_le l.labels]
  have count : (∑ c ∈ range l.cells, (directoryRows l m c).length) ≤ 2*l.cableCount :=
    incidence_count_le _ _ _
  have scan := assignmentTicks_le (setupSlots := RoutingISA.LabelTrial.setup.slots) (by decide) z l.cells
    (fun c => (directoryRows l m c).length)
  rw [← hz] at scan
  have nn := Nat.le_mul_of_pos_right n one
  have kk := Nat.le_mul_of_pos_left k pos
  have init := initTicks_le l
  have a : initTicks l ≤ 126*(n*k) := by have hn : n = 1+l.cells+l.cableCount+l.deliveryCount := rfl; omega
  have c : 1+l.cells+(∑ i ∈ range l.cells, (directoryRows l m i).length) ≤ 2*n := by dsimp [n]; omega
  have b := (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 200 c))
  change directoryTicks l z m ≤ 600*n*k
  unfold directoryTicks
  calc
    _ ≤ 126*(n*k)+(200*(2*n))*k := Nat.add_le_add a (scan.trans b)
    _ = 526*(n*k) := by ring
    _ ≤ 600*n*k := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)

/-- The physical rate obeys the manuscript's scan envelope for sparse descriptor counts. -/
theorem directoryTicks_le_envelope (l : Layout) (m : ℕ → ℕ) (z B degree : ℕ) (hz : l.labels = z+1)
    (counts : 1+l.cells+l.cableCount+l.deliveryCount ≤ B*(l.cells+1)*(degree+1)) :
    directoryTicks l z m ≤ MeanChoice.scanEnvelope (600*B) l.cells degree l.labels := by
  apply (directoryTicks_le l m z hz).trans
  have h := Nat.mul_le_mul (Nat.mul_le_mul_left 600 counts)
    (Nat.pow_le_pow_right (show 0 < l.labels+1 by omega) (show 3 ≤ 6 by decide))
  simpa only [MeanChoice.scanEnvelope,Nat.mul_assoc] using h

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
