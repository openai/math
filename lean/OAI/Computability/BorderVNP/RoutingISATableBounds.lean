import OAI.Computability.BorderVNP.RoutingISATableModel

/-! # Address and width bounds of the physical scheduling arrays -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open Finset

variable {l : TableLayout} {w : ℕ}

/-- Row-major addresses below a pair of in-range team indices fit in the square table. -/
theorem pairKey_bound {u v : ℕ} (hu : u < l.teams) (hv : v < l.teams) :
    u*l.teams+v < l.teams^2 := by
  calc
    u*l.teams+v < (u+1)*l.teams := by rw [Nat.add_mul]; omega
    _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul_right _ hu

/-- A row-major triple address lies below the cubic table length. -/
theorem tripleKey_bound {u v j : ℕ} (hu : u < l.teams) (hv : v < l.teams) (hj : j < l.teams) :
    (u*l.teams+v)*l.teams+j < l.teams^3 := by
  calc
    _ < (u*l.teams+v+1)*l.teams := by rw [Nat.add_mul (u*l.teams+v) 1 l.teams, one_mul]; omega
    _ ≤ _ := by rw [pow_succ]; exact Nat.mul_le_mul_right _ (pairKey_bound hu hv)

/-- Unordered pair addresses occupy the declared square table. -/
theorem TableLayout.pairKey_lt {u v : ℕ} (hu : u < l.teams) (hv : v < l.teams) :
    l.pairKey u v < l.teams^2 := pairKey_bound ((min_le_left ..).trans_lt hu) (max_lt hu hv)

/-- Every interval member represents an actual word address. -/
theorem TableLayout.Allocated.address {a : TableArray} {i : ℕ} (al : l.Allocated w) (hi : l.contains a i) :
    i < 2^w := hi.2.trans_le (al.fits a)

/-- The record count itself fits, since each actual record occupies seven words. -/
theorem TableLayout.Allocated.countFits (al : l.Allocated w) : l.count < 2^w := by
  have h : l.records+7*l.count ≤ 2^w := al.fits .records
  have : 0 < 2^w := by positivity
  omega

/-- The one-word squared loop bound covers the team count. -/
theorem TableLayout.Allocated.teamsFit (al : l.Allocated w) : l.teams < 2^w :=
  (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans_lt al.square

/-- Every proper prefix of the oriented leg table is bounded by its terminal total. -/
theorem TableLayout.legPrefix_mono (l : TableLayout) (row : ℕ → TableRow) (u v : ℕ)
    {j k : ℕ} (h : j ≤ k) : l.legPrefix row u v j ≤ l.legPrefix row u v k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) fun _ _ _ => Nat.zero_le _

/-- Cumulative pair width is monotone as more transmission records are scanned. -/
theorem TableLayout.pairWidth_mono (l : TableLayout) (row : ℕ → TableRow) (key : ℕ)
    {i j : ℕ} (h : i ≤ j) : l.pairWidth row i key ≤ l.pairWidth row j key :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) fun _ _ _ => Nat.zero_le _

/-- A nonlocal record's whole interval fits in the unordered-pair table entry
at the end of the scheduling pass. -/
theorem TableLayout.ordinal_add_width_le (l : TableLayout) (row : ℕ → TableRow) {i : ℕ}
    (hi : i < l.count) (hn : (row i).first ≠ (row i).second) :
    l.ordinal row i + (row i).width ≤
      l.pairWidth row l.count (l.pairKey (row i).first (row i).second) := by
  have h := l.pairWidth_mono row (l.pairKey (row i).first (row i).second) (i := i+1) hi
  simpa [TableLayout.ordinal, TableLayout.pairWidth, Finset.sum_range_succ, hn] using h

/-- Distinct nonlocal intervals on the same unordered pair occupy disjoint ordinal ranges. -/
theorem TableLayout.ordinal_order (l : TableLayout) (row : ℕ → TableRow) {i j : ℕ}
    (hij : i < j) (hi : (row i).first ≠ (row i).second) (hj : (row j).first ≠ (row j).second)
    (he : l.pairKey (row i).first (row i).second = l.pairKey (row j).first (row j).second) :
    l.ordinal row i + (row i).width ≤ l.ordinal row j := by
  have h := l.pairWidth_mono row (l.pairKey (row i).first (row i).second) (i := i+1) hij
  simpa [TableLayout.ordinal, TableLayout.pairWidth, Finset.sum_range_succ, hi, hj, ← he] using h

private theorem stride_le (period start width : ℕ) : Routing.strideCount period start width ≤ width := by
  unfold Routing.strideCount
  split
  · omega
  · have h := Nat.div_le_self (width-1-start) period
    omega

private theorem length_le (l : TableLayout) (row : ℕ → TableRow) (u v j : ℕ) :
    l.partnerLength row u v j ≤ l.pairWidth row l.count (l.pairKey u j) := by
  unfold TableLayout.partnerLength
  split
  · rw [Routing.scheduledLength_formula]
    split
    · exact stride_le ..
    · omega
  · omega

private theorem key_injective {u : ℕ} (hu : u < l.teams) {j k : ℕ} (hj : j < l.teams)
    (hk : k < l.teams) (h : l.pairKey u j = l.pairKey u k) : j = k := by
  have hq := congrArg (· / l.teams) h
  have hr := congrArg (· % l.teams) h
  have pos : 0 < l.teams := by omega
  change (min u j*l.teams+max u j)/l.teams = (min u k*l.teams+max u k)/l.teams at hq
  change (min u j*l.teams+max u j)%l.teams = (min u k*l.teams+max u k)%l.teams at hr
  rw [Nat.mul_comm (min u j), Nat.mul_comm (min u k)] at hq
  simp only [Nat.mul_add_div pos, Nat.div_eq_of_lt (max_lt hu hj),
    Nat.div_eq_of_lt (max_lt hu hk), Nat.add_zero] at hq
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (max_lt hu hj),
    Nat.mod_eq_of_lt (max_lt hu hk)] at hr
  omega

/-- An oriented leg never carries more bits than the sum of all transmission widths.
For a fixed endpoint, a record can contribute to at most one partner's length. -/
theorem TableLayout.legPrefix_le_sum (l : TableLayout) (row : ℕ → TableRow) {u : ℕ}
    (hu : u < l.teams) (v : ℕ) :
    l.legPrefix row u v l.teams ≤ ∑ j ∈ range l.count, (row j).width := by
  apply (Finset.sum_le_sum fun j (_ : j ∈ range l.teams) => length_le l row u v j).trans
  simp only [TableLayout.pairWidth]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : ∃ j ∈ range l.teams, (row i).first ≠ (row i).second ∧
      l.pairKey (row i).first (row i).second = l.pairKey u j
  · obtain ⟨j,hj,hq⟩ := h
    rw [Finset.sum_eq_single_of_mem j hj]
    · simp [hq]
    · intro k hk hkj
      split
      next h => exact (hkj (key_injective hu (Finset.mem_range.mp hk) (Finset.mem_range.mp hj) (h.2.symm.trans hq.2))).elim
      next => rfl
  · have hz : ∀ j ∈ range l.teams, ¬ ((row i).first ≠ (row i).second ∧
        l.pairKey (row i).first (row i).second = l.pairKey u j) := fun j hj hcond => h ⟨j,hj,hcond⟩
    rw [Finset.sum_eq_zero fun j hj => ite_eq_right (hz j hj)]
    exact Nat.zero_le _

end RoutingISA

end BorderVNP
end Computability
end OAI
