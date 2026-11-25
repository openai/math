import OAI.LinearAlgebra.FiniteFourier.GridPartition
import OAI.LinearAlgebra.FiniteFourier.CircuitParallel
import OAI.LinearAlgebra.FiniteFourier.OccupiedAxes
import OAI.LinearAlgebra.FiniteFourier.WorkingGroup

/-! # Reassembling the grouped transforms on the original grid of coordinates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open Finset Matrix

variable {K : Type*} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : ι → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
  (A : ∀ i, Matrix (P i) (P i) K)

/-- Apply exactly the factors indexed by `S` on the full grid. -/
def partialGrid (S : Finset ι) : Matrix (∀ i, P i) (∀ i, P i) K :=
  gridTensor (fun i ↦ if i ∈ S then A i else 1)

/-- A group transform in parallel for all settings of the complementary coordinates. -/
def fiberGrid (S : Finset ι) :=
  Matrix.blockDiagonal (fun _ : (∀ i : {i // i ∉ S}, P i.val) ↦
    gridTensor (fun i : S ↦ A i.val))

omit [∀ i, Fintype (P i)] in
theorem partialGrid_eq_fiberGrid (S : Finset ι) :
    partialGrid A S = (fiberGrid A S).submatrix
      (Equiv.piEquivPiSubtypeProd (· ∈ S) P) (Equiv.piEquivPiSubtypeProd (· ∈ S) P) := by
  classical
  ext x y
  rw [Matrix.submatrix_apply, fiberGrid, Matrix.blockDiagonal_apply]
  change (∏ i, (if i ∈ S then A i else 1) (x i) (y i)) =
    if (fun i : {i // i ∉ S} ↦ x i.val) = (fun i : {i // i ∉ S} ↦ y i.val) then
      ∏ i : S, A i.val (x i) (y i) else 0
  have hp (i : S) : (if i.val ∈ S then A i.val else 1) (x i) (y i) =
      A i.val (x i) (y i) := by rw [ite_eq_left i.property]
  have hn (i : {i // i ∉ S}) : (if i.val ∈ S then A i.val else 1) (x i) (y i) =
      (1 : Matrix (P i.val) (P i.val) K) (x i) (y i) := by rw [ite_eq_right i.property]
  rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ S)]
  simp_rw [hp, hn]
  split_ifs with h
  · have hx (i : {i // i ∉ S}) : x i = y i := congrFun h i
    have hid : (∏ i : {i // i ∉ S}, (1 : Matrix (P i.val) (P i.val) K) (x i) (y i)) = 1 :=
      Finset.prod_eq_one (fun i _ ↦ by rw [hx i, Matrix.one_apply_eq])
    rw [hid, mul_one]
    exact Finset.prod_congr (by ext; simp) (fun _ _ ↦ rfl)
  · obtain ⟨i, hi⟩ : ∃ i : {i // i ∉ S}, x i.val ≠ y i.val := by
      contrapose! h
      exact funext h
    have hid : (∏ j : {i // i ∉ S}, (1 : Matrix (P j.val) (P j.val) K) (x j) (y j)) = 0 :=
      Finset.prod_eq_zero (mem_univ i) (Matrix.one_apply_ne hi)
    rw [hid, mul_zero]

theorem partialGrid_disjoint_mul {S T : Finset ι} (h : Disjoint S T) :
    partialGrid A S * partialGrid A T = partialGrid A (S ∪ T) := by
  rw [partialGrid, partialGrid, partialGrid, ← gridTensor_mul]
  apply congrArg gridTensor
  funext i
  by_cases hs : i ∈ S
  · simp [hs, Finset.disjoint_left.mp h hs]
  · by_cases ht : i ∈ T <;> simp [hs, ht]

/-- The single-axis matrix is run once per complementary fiber. -/
theorem axis_realizable_on_full_grid (i : ι) :
    RealizableAtMost (partialGrid A {i})
      (Fintype.card (∀ j : {j // j ≠ i}, P j.val) * complexity (A i)) := by
  have hid : partialGrid A {i} = axisMatrix A i := by simp [partialGrid, axisMatrix]
  rw [hid, axisMatrix_eq_blockDiagonal]
  exact (((complexity_le_iff ..).mp le_rfl).blockDiagonal _).submatrix
    (Equiv.piSplitAt i P) (Equiv.piSplitAt i P).toEmbedding

private theorem realizable_partialGrid_list (gs : List (List ι)) (hn : gs.flatten.Nodup)
    (C : ℕ) (hb : ∀ g ∈ gs, RealizableAtMost (partialGrid A g.toFinset) C) :
    RealizableAtMost (partialGrid A gs.flatten.toFinset) (gs.length * C) := by
  induction gs with
  | nil =>
    simp only [List.flatten_nil, List.toFinset_nil, partialGrid, Finset.notMem_empty,
      ite_false, gridTensor_one, List.length_nil, Nat.zero_mul]
    refine ⟨0, le_rfl, ⟨.nil, fun i ↦ .scaled 1 (.inl i)⟩, ?_⟩
    ext i j
    simp [Circuit.matrix, Circuit.eval, Readout.eval, Matrix.one_apply, Pi.single_apply]
  | cons g gs ih =>
    simp only [List.flatten_cons, List.nodup_append] at hn
    have hd : Disjoint g.toFinset gs.flatten.toFinset := by
      apply Finset.disjoint_left.mpr
      intro i hi hi'
      exact hn.2.2 i (List.mem_toFinset.mp hi) i (List.mem_toFinset.mp hi') rfl
    rw [List.flatten_cons, List.toFinset_append, ← partialGrid_disjoint_mul A hd]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (hb g (.head _)).mul (ih hn.2.1 (fun d hm ↦ hb d (.tail _ hm)))

/-- If every large axis and every small group costs at most `C` on all its fibers,
the circuit for the original (unpermuted) tensor product costs at most `25*C`. -/
theorem complexity_gridTensor_of_partition {N C : ℕ} {xs : List ι}
    (w : GridPartition (fun i ↦ Fintype.card (P i)) N xs)
    (hxs : xs.Perm (Finset.univ : Finset ι).toList) (hN : 1 < N)
    (hv : axisVolume (fun i ↦ Fintype.card (P i)) xs = N)
    (hlarge : ∀ i ∈ w.large, Fintype.card (∀ j : {j // j ≠ i}, P j.val) * complexity (A i) ≤ C)
    (hsmall : ∀ g ∈ w.rest :: w.full, complexity (fiberGrid A g.toFinset) ≤ C) :
    complexity (gridTensor A) ≤ 25 * C := by
  let gs := (w.large.map (fun i ↦ [i])) ++ w.rest :: w.full
  have hflat : gs.flatten.Perm (Finset.univ : Finset ι).toList := by
    have hs (l : List ι) : (l.map (fun i ↦ [i])).flatten = l := by induction l <;> simp_all
    simpa [gs, hs] using w.covers.trans hxs
  have hparts := realizable_partialGrid_list A gs (hflat.nodup_iff.mpr (Finset.nodup_toList _)) C
  have hcost : RealizableAtMost (partialGrid A gs.flatten.toFinset) (gs.length * C) := by
    apply hparts
    intro g hg
    rcases List.mem_append.mp hg with hl | hs
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
      apply (complexity_le_iff ..).mp
      exact ((complexity_le_iff ..).mpr (axis_realizable_on_full_grid A i)).trans (hlarge i hi)
    · rw [partialGrid_eq_fiberGrid]
      exact ((complexity_le_iff ..).mp (hsmall g hs)).submatrix
        (Equiv.piEquivPiSubtypeProd (· ∈ g.toFinset) P)
        (Equiv.piEquivPiSubtypeProd (· ∈ g.toFinset) P).toEmbedding
  have hall : gs.flatten.toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, hflat.mem_iff, Finset.mem_toList]
  have hid : partialGrid A gs.flatten.toFinset = gridTensor A := by simp [hall, partialGrid]
  rw [hid] at hcost
  apply ((complexity_le_iff ..).mpr hcost).trans
  have hlen := w.length_le hN hv
  apply Nat.mul_le_mul_right
  simp [gs]
  omega

/-- Apply the greedy partition and compose the local circuits. The small-group
estimate is needed only at volumes satisfying the extension-capacity threshold. -/
theorem complexity_gridTensor_of_group_bounds {N C : ℕ} (hN : 1 < N)
    (hvol : ∏ i, Fintype.card (P i) = N)
    (hlarge : ∀ i, N < Fintype.card (P i) ^ 24 →
      Fintype.card (∀ j : {j // j ≠ i}, P j.val) * complexity (A i) ≤ C)
    (hsmall : ∀ S : Finset ι, (∀ i ∈ S, Fintype.card (P i) ^ 24 ≤ N) →
      (∏ i : S, Fintype.card (P i.val)) ^ 12 ≤ N → complexity (fiberGrid A S) ≤ C) :
    complexity (gridTensor A) ≤ 25 * C := by
  let xs := (univ : Finset ι).toList
  let a (i : ι) := Fintype.card (P i)
  obtain ⟨w⟩ := exists_gridPartition a hN xs
  have hxs : xs.Nodup := Finset.nodup_toList _
  have hv : axisVolume a xs = N := by
    rw [axisVolume, ← List.prod_toFinset a hxs]
    simpa [xs, a] using hvol
  apply complexity_gridTensor_of_partition A w (.refl _) hN hv
    (fun i hi ↦ hlarge i (w.large_spec i hi))
  intro g hg
  have hsmallmem : ∀ i ∈ g, i ∈ w.rest ++ w.full.flatten := by
    intro i hi
    rcases List.mem_cons.mp hg with rfl | hf
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_flatten.mpr ⟨g, hf, hi⟩)
  have hnd := (List.nodup_append.mp (w.covers.nodup_iff.mpr hxs)).2.1
  have hgn : g.Nodup := by
    rcases List.mem_cons.mp hg with rfl | hf
    · exact (List.nodup_append.mp hnd).1
    · exact (List.nodup_flatten.mp (List.nodup_append.mp hnd).2.1).1 _ hf
  apply hsmall g.toFinset
  · exact fun i hi ↦ w.small_spec _ (hsmallmem _ (List.mem_toFinset.mp hi))
  · change (∏ i : g.toFinset, a i.val) ^ 12 ≤ N
    rw [Finset.prod_coe_sort, List.prod_toFinset a hgn]
    rcases List.mem_cons.mp hg with rfl | hf
    · exact w.rest_upper
    · exact w.full_upper g hf

omit [∀ i, DecidableEq (P i)] in
/-- The complementary coordinate tuple has exactly `N/B` settings. -/
theorem card_group_complement (S : Finset ι) {N : ℕ} (hvol : ∏ i, Fintype.card (P i) = N)
    (hp : ∀ i ∈ S, 0 < Fintype.card (P i)) :
    Fintype.card (∀ j : {j // j ∉ S}, P j.val) = N / (∏ i : S, Fintype.card (P i.val)) := by
  have hprod := Fintype.prod_subtype_mul_prod_subtype (· ∈ S) (fun i ↦ Fintype.card (P i))
  rw [hvol] at hprod
  have hpos : 0 < ∏ i : S, Fintype.card (P i.val) := Finset.prod_pos fun i _ ↦ hp _ i.property
  have heq : (∏ i : S, Fintype.card (P i.val)) *
      (∏ j : {j // j ∉ S}, Fintype.card (P j.val)) = N := by
    convert! hprod using 2
    exact Finset.prod_congr (by ext; simp) (fun _ _ ↦ rfl)
  rw [← heq, Nat.mul_div_cancel_left _ hpos, Fintype.card_pi]

/-- Replace the complementary-coordinate labels by a compact batch index for
use with the scalar-descent circuit. This reindexing costs no gates. -/
theorem complexity_fiberGrid_eq_fin (S : Finset ι) {h : ℕ}
    (hc : Fintype.card (∀ j : {j // j ∉ S}, P j.val) = h) :
    complexity (fiberGrid A S) = complexity (Matrix.blockDiagonal (fun _ : Fin h ↦
      gridTensor (fun i : S ↦ A i.val))) := by
  let e := Fintype.equivFinOfCardEq hc
  let q := (Equiv.refl (∀ i : S, P i.val)).prodCongr e
  rw [← complexity_reindex (fiberGrid A S) q q]
  congr 1
  ext ⟨x,i⟩ ⟨y,j⟩
  by_cases hij : i = j
  · subst j
    simp [q, fiberGrid, Matrix.reindex_apply, Matrix.blockDiagonal_apply]
  · simp [q, fiberGrid, Matrix.reindex_apply, Matrix.blockDiagonal_apply, hij]

/-- Real-valued gate budgets on the large axes and descended small blocks assemble
with the same factor 25. The small-group costs here use `Fin (N/B)`, matching
the packed scalar-descent theorem. -/
theorem complexity_gridTensor_of_batch_bounds {N : ℕ} {C : ℝ} (hN : 1 < N) (hC : 0 ≤ C)
    (hvol : ∏ i, Fintype.card (P i) = N) (hp : ∀ i, 0 < Fintype.card (P i))
    (hlarge : ∀ i, N < Fintype.card (P i) ^ 24 →
      (Fintype.card (∀ j : {j // j ≠ i}, P j.val) : ℝ) * complexity (A i) ≤ C)
    (hsmall : ∀ S : Finset ι, (∀ i ∈ S, Fintype.card (P i) ^ 24 ≤ N) →
      (∏ i : S, Fintype.card (P i.val)) ^ 12 ≤ N →
      (complexity (Matrix.blockDiagonal (fun _ : Fin (N / (∏ i : S, Fintype.card (P i.val))) ↦
        gridTensor (fun i : S ↦ A i.val))) : ℝ) ≤ C) :
    (complexity (gridTensor A) : ℝ) ≤ 25 * C := by
  have hg : complexity (gridTensor A) ≤ 25 * ⌊C⌋₊ := by
    apply complexity_gridTensor_of_group_bounds A hN hvol
    · intro i hi
      exact Nat.le_floor (by simpa only [Nat.cast_mul] using hlarge i hi)
    · intro S hs hB
      apply Nat.le_floor
      rw [complexity_fiberGrid_eq_fin A S (card_group_complement S hvol (fun i _ ↦ hp i))]
      exact hsmall S hs hB
  calc
    (complexity (gridTensor A) : ℝ) ≤ 25 * (⌊C⌋₊ : ℝ) := by exact_mod_cast hg
    _ ≤ 25 * C := mul_le_mul_of_nonneg_left (Nat.floor_le hC) (by norm_num)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
