import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # Stable compaction of selected Boolean rows -/

namespace ThreeFlat.Routing.StableCompaction

/-- The rows selected by a Boolean mask. -/
def active {n : ℕ} (M : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => M i = true

@[simp] theorem mem_active {n : ℕ} {M : Fin n → Bool} {i : Fin n} :
    i ∈ active M ↔ M i = true := by simp [active]

/-- Selected data in increasing input order, padded on the right by zeros. -/
noncomputable def compact {n : ℕ} (M X : Fin n → Bool) (j : Fin n) : Bool :=
  if h : j.val < (active M).card then X ((active M).orderEmbOfFin rfl ⟨j.val,h⟩) else false

/-- Number of selected rows strictly before an input row. -/
def prefixCount {n : ℕ} (M : Fin n → Bool) (i : Fin n) : ℕ :=
  ((active M).filter (· < i)).card

/-- The inverse increasing enumeration of a selected row counts its selected predecessors. -/
theorem orderIndex_eq_prefixCount {n : ℕ} (M : Fin n → Bool) (i : active M) :
    (((active M).orderIsoOfFin rfl).symm i).val = prefixCount M i.val := by
  let e := (active M).orderIsoOfFin rfl
  change (e.symm i).val = _
  rw [← Fin.card_Iio]
  apply Finset.card_bij (fun j _ => (e j).val)
  · intro j hj
    refine Finset.mem_filter.mpr ⟨(e j).property, ?_⟩
    change e j < i
    exact (e.lt_iff_lt.mpr (Finset.mem_Iio.mp hj)).trans_eq (e.apply_symm_apply i)
  · intro j _ k _ h
    exact e.injective (Subtype.ext h)
  · intro j hj
    let k : active M := ⟨j, (Finset.mem_filter.mp hj).1⟩
    exact ⟨e.symm k, Finset.mem_Iio.mpr
      (e.symm.lt_iff_lt.mpr (show k < i from (Finset.mem_filter.mp hj).2)),
      congrArg Subtype.val (e.apply_symm_apply k)⟩

theorem prefixCount_lt_card {n : ℕ} {M : Fin n → Bool} {i : Fin n} (hi : M i = true) :
    prefixCount M i < (active M).card := by
  let a : active M := ⟨i, mem_active.mpr hi⟩
  rw [← orderIndex_eq_prefixCount M a]
  exact (((active M).orderIsoOfFin rfl).symm a).isLt

/-- Selecting at the prefix count recovers that input row. -/
theorem select_prefixCount {n : ℕ} {M : Fin n → Bool} {i : Fin n} (hi : M i = true) :
    (active M).orderEmbOfFin rfl ⟨prefixCount M i, prefixCount_lt_card hi⟩ = i := by
  let a : active M := ⟨i, mem_active.mpr hi⟩
  let e := (active M).orderIsoOfFin rfl
  have h : (⟨prefixCount M i, prefixCount_lt_card hi⟩ : Fin (active M).card) = e.symm a :=
    Fin.ext (orderIndex_eq_prefixCount M a).symm
  rw [h]
  exact congrArg Subtype.val (e.apply_symm_apply a)

/-- Each occupied output address has a unique selected input row. -/
theorem existsUnique_active_of_prefixCount {n : ℕ} (M : Fin n → Bool) (j : Fin (active M).card) :
    ∃! i, M i = true ∧ prefixCount M i = j.val := by
  let e := (active M).orderIsoOfFin rfl
  refine ⟨(e j).val, ⟨mem_active.mp (e j).property, ?_⟩, ?_⟩
  · exact (orderIndex_eq_prefixCount M (e j)).symm.trans (congrArg Fin.val (e.symm_apply_apply j))
  · rintro i ⟨hi, hcount⟩
    have h : (⟨prefixCount M i, prefixCount_lt_card hi⟩ : Fin (active M).card) = j :=
      Fin.ext hcount
    have hx := select_prefixCount hi
    rw [h] at hx
    exact hx.symm

/-- Reading a selected row at its compacted address preserves its data bit. -/
theorem compact_at_prefixCount {n : ℕ} (M X : Fin n → Bool) {i j : Fin n}
    (hi : M i = true) (hj : j.val = prefixCount M i) : compact M X j = X i := by
  have hlt : j.val < (active M).card := hj ▸ prefixCount_lt_card hi
  simp only [compact, hlt, ↓reduceDIte]
  have h : (⟨j.val, hlt⟩ : Fin (active M).card) =
      ⟨prefixCount M i, prefixCount_lt_card hi⟩ := Fin.ext hj
  rw [h, select_prefixCount hi]

@[simp] theorem compact_after {n : ℕ} (M X : Fin n → Bool) (j : Fin n)
    (hj : (active M).card ≤ j.val) : compact M X j = false := by
  simp [compact, Nat.not_lt.mpr hj]


/-- Position of a selected row in the padded compacted array. -/
def outputIndex {n : ℕ} {M : Fin n → Bool} {i : Fin n} (hi : M i = true) : Fin n :=
  ⟨prefixCount M i, (prefixCount_lt_card hi).trans_le
    ((active M).card_le_univ.trans_eq (Fintype.card_fin n))⟩

/-- Move the packed bits back to their selected input rows, filling inactive
rows with zero. -/
def expand {n : ℕ} (M Y : Fin n → Bool) (i : Fin n) : Bool :=
  if hi : M i = true then Y (outputIndex hi) else false

/-- Expansion recovers all input bits whenever inactive rows carry zero. -/
theorem expand_compact {n : ℕ} (M X : Fin n → Bool)
    (support : ∀ i, M i = false → X i = false) : expand M (compact M X) = X := by
  funext i
  cases hi : M i with
  | false => simp [expand, hi, support i hi]
  | true =>
    simp only [expand, hi, ↓reduceDIte]
    exact compact_at_prefixCount M X hi rfl

/-- Compaction recovers the packed array when all unused tail rows are zero. -/
theorem compact_expand {n : ℕ} (M Y : Fin n → Bool)
    (pad : ∀ j : Fin n, (active M).card ≤ j.val → Y j = false) : compact M (expand M Y) = Y := by
  funext j
  by_cases hj : j.val < (active M).card
  · let e := (active M).orderIsoOfFin rfl
    let k : Fin (active M).card := ⟨j.val,hj⟩
    let i := (e k).val
    have hi : M i = true := mem_active.mp (e k).property
    have hk : prefixCount M i = j.val :=
      (orderIndex_eq_prefixCount M (e k)).symm.trans (congrArg Fin.val (e.symm_apply_apply k))
    rw [compact_at_prefixCount M (expand M Y) hi hk.symm]
    simp only [expand, hi, ↓reduceDIte]
    exact congrArg Y (Fin.ext hk)
  · rw [compact_after _ _ _ (Nat.le_of_not_gt hj), pad _ (Nat.le_of_not_gt hj)]

/-- Each zero-padded output has exactly one preimage supported on the mask. -/
theorem existsUnique_supported_preimage {n : ℕ} (M Y : Fin n → Bool)
    (pad : ∀ j : Fin n, (active M).card ≤ j.val → Y j = false) :
    ∃! X : Fin n → Bool, (∀ i, M i = false → X i = false) ∧ compact M X = Y := by
  refine ⟨expand M Y, ⟨?_, compact_expand M Y pad⟩, ?_⟩
  · intro i hi
    simp [expand, hi]
  · rintro X ⟨support, hX⟩
    rw [← hX]
    exact (expand_compact M X support).symm


end ThreeFlat.Routing.StableCompaction

end OAI
