import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! # Weighted quantiles used to charge a failed price trial

The vertices with positive surplus are listed in decreasing surplus order. Their
masses subdivide an interval. The first half-band supplies a common feedback set,
and the next half-band distributes the pivot probability. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The left endpoint of the interval belonging to entry `i`. -/
def massBefore (w : ℕ → K) (i : ℕ) : K := ∑ j ∈ range i, w j

/-- Projection of a point onto the interval from `a` to `b`. -/
private def clip (a b x : K) : K := min (max x a) b

/-- Length of the intersection of the interval belonging to `i` with `[a,b]`. -/
def bandMass (w : ℕ → K) (a b : K) (i : ℕ) : K :=
  clip a b (massBefore w (i + 1)) - clip a b (massBefore w i)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem massBefore_succ (w : ℕ → K) (i : ℕ) :
    massBefore w (i + 1) = massBefore w i + w i := sum_range_succ _ _

private theorem massBefore_mono {w : ℕ → K} {n i j : ℕ} (hw : ∀ k < n, 0 ≤ w k)
    (hij : i ≤ j) (hjn : j ≤ n) : massBefore w i ≤ massBefore w j := by
  apply sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hij)
  intro k hk _
  exact hw k ((mem_range.mp hk).trans_le hjn)

private theorem clip_incr {a b x y : K} (hxy : x ≤ y) :
    0 ≤ clip a b y - clip a b x ∧ clip a b y - clip a b x ≤ y - x := by
  simp only [clip, min_def, max_def]
  split_ifs <;> constructor <;> linarith

private theorem bandMass_bounds {w : ℕ → K} (a b : K) {i : ℕ} (hw : 0 ≤ w i) :
    0 ≤ bandMass w a b i ∧ bandMass w a b i ≤ w i := by
  simpa only [bandMass, massBefore_succ, add_sub_cancel_left] using
    (clip_incr (a := a) (b := b) (x := massBefore w i) (le_add_of_nonneg_right hw))

private theorem bandMass_pos {w : ℕ → K} {a b : K} {i : ℕ} (hab : a ≤ b)
    (h : 0 < bandMass w a b i) : massBefore w i < b ∧ a < massBefore w (i + 1) := by
  simp only [bandMass, clip, min_def, max_def] at h
  split_ifs at h <;> constructor <;> linarith

omit [IsStrictOrderedRing K] in
private theorem sum_bandMass {w : ℕ → K} {a b : K} {n : ℕ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ massBefore w n) :
    ∑ i ∈ range n, bandMass w a b i = b - a := by
  unfold bandMass
  rw [sum_range_sub (fun i => clip a b (massBefore w i)) n]
  have hzero : massBefore w 0 = 0 := by simp [massBefore]
  simp only [clip, hzero, max_eq_right ha, min_eq_left hab,
    min_eq_right (hb.trans (le_max_left _ a))]

/-- Normalized intersection length with the band `(δ/2, δ)`. -/
def pivotProbability (w : ℕ → K) (δ : K) (i : ℕ) : K :=
  bandMass w (δ / 2) δ i / (δ / 2)

/-- Positive-surplus vertices whose intervals meet `(0,δ/2)` in positive length. -/
def feedbackSet (w : ℕ → K) (δ : K) (n : ℕ) : Finset ℕ :=
  (range n).filter (fun i => 0 < bandMass w 0 (δ / 2) i)

/-- For every pivot in the probability support, mass strictly above its surplus is
less than `δ`. The same top set, of mass at least `δ/2`, is at least as good as
*every* such pivot, even if equal surpluses were ordered arbitrarily. -/
theorem quantile_pivots {n : ℕ} {w surplus : ℕ → K} {δ : K}
    (hw : ∀ i < n, 0 ≤ w i) (hs : ∀ i < n, ∀ j < n, i ≤ j → surplus j ≤ surplus i)
    (hδ : 0 < δ) (hm : δ ≤ massBefore w n) :
    (∑ i ∈ range n, pivotProbability w δ i) = 1 ∧
    (∀ i < n, 0 ≤ pivotProbability w δ i ∧ pivotProbability w δ i ≤ 2 * w i / δ) ∧
    δ / 2 ≤ ∑ i ∈ feedbackSet w δ n, w i ∧
    ∀ i < n, 0 < pivotProbability w δ i →
      (∑ j ∈ (range n).filter (fun j => surplus i < surplus j), w j) < δ ∧
      ∀ j ∈ feedbackSet w δ n, surplus i ≤ surplus j := by
  have hd : 0 < δ / 2 := by positivity
  have hle : δ / 2 ≤ δ := by linarith
  have htop := sum_bandMass (w := w) (a := 0) (n := n) (b := δ / 2)
    le_rfl hd.le (hle.trans hm)
  have hmid := sum_bandMass (w := w) hd.le hle hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [pivotProbability, ← sum_div, hmid]
    field_simp
    ring
  · intro i hi
    obtain ⟨hn, hu⟩ := bandMass_bounds (δ / 2) δ (hw i hi)
    refine ⟨div_nonneg hn hd.le, ?_⟩
    calc
      pivotProbability w δ i ≤ w i / (δ / 2) := div_le_div_of_nonneg_right hu hd.le
      _ = 2 * w i / δ := by ring
  · rw [sub_zero] at htop
    calc
      δ / 2 = ∑ i ∈ range n, bandMass w 0 (δ / 2) i := htop.symm
      _ = ∑ i ∈ feedbackSet w δ n, bandMass w 0 (δ / 2) i := by
        symm
        apply sum_subset (filter_subset _ _)
        intro i hi hnot
        have hnonneg := (bandMass_bounds 0 (δ / 2) (hw i (mem_range.mp hi))).1
        have hnonpos : ¬ 0 < bandMass w 0 (δ / 2) i := fun hp => hnot (mem_filter.mpr ⟨hi, hp⟩)
        exact le_antisymm (le_of_not_gt hnonpos) hnonneg
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        exact (bandMass_bounds 0 (δ / 2) (hw i (mem_range.mp (mem_filter.mp hi).1))).2
  · intro i hi hp
    have hband : 0 < bandMass w (δ / 2) δ i :=
      (div_pos_iff_of_pos_right hd).mp hp
    obtain ⟨hstart, hend⟩ := bandMass_pos hle hband
    constructor
    · apply lt_of_le_of_lt _ hstart
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        obtain ⟨hjn, hsur⟩ := mem_filter.mp hj
        exact mem_range.mpr (lt_of_not_ge (fun hij => (not_lt_of_ge (hs i hi j (mem_range.mp hjn) hij)) hsur))
      · intro j hj _
        exact hw j ((mem_range.mp hj).trans hi)
    · intro j hj
      obtain ⟨hjn, hbandj⟩ := mem_filter.mp hj
      have hbefore := (bandMass_pos hd.le hbandj).1
      apply hs j (mem_range.mp hjn) i hi
      by_contra! hlt
      have := massBefore_mono hw (show i + 1 ≤ j from hlt) (mem_range.mp hjn).le
      linarith

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem sum_reindex {V : Type*} [Fintype V] {n : ℕ} (e : Fin n ≃ V)
    {f : ℕ → K} {g : V → K} (h : ∀ i : Fin n, f i = g (e i)) :
    ∑ i ∈ range n, f i = ∑ v, g v := by
  calc
    _ = ∑ i : Fin n, f i := (Fin.sum_univ_eq_sum_range f n).symm
    _ = ∑ i : Fin n, g (e i) := sum_congr rfl (fun i _ => h i)
    _ = ∑ v, g v := e.sum_comp g

/-- The pivot distribution and its common feedback set on an unordered finite
type. Use the type of active positive-surplus vertices to apply the construction
at a probe; `score` is the surplus. -/
theorem exists_quantile_pivots {V : Type*} [Fintype V] [DecidableEq V]
    (w score : V → K) {δ : K} (hw : ∀ v, 0 ≤ w v) (hδ : 0 < δ)
    (hm : δ ≤ ∑ v, w v) :
    ∃ (p : V → K) (top : Finset V),
      ∑ v, p v = 1 ∧ (∀ v, 0 ≤ p v ∧ p v ≤ 2 * w v / δ) ∧
      δ / 2 ≤ ∑ v ∈ top, w v ∧
      ∀ v, 0 < p v →
        (∑ j ∈ univ.filter (fun j => score v < score j), w j) < δ ∧
        ∀ j ∈ top, score v ≤ score j := by
  classical
  let n := Fintype.card V
  let h : Fin n ≃ V := (Fintype.equivFin V).symm
  let f (i : Fin n) : Kᵒᵈ := OrderDual.toDual (score (h i))
  let e : Fin n ≃ V := (Tuple.sort f).trans h
  have horder : Antitone (score ∘ e) := Tuple.monotone_sort f
  let W (k : ℕ) := if hk : k < n then w (e ⟨k, hk⟩) else 0
  let S (k : ℕ) := if hk : k < n then score (e ⟨k, hk⟩) else 0
  have hW (i : Fin n) : W i = w (e i) := by simp [W]
  have hS (i : Fin n) : S i = score (e i) := by simp [S]
  have data := quantile_pivots (w := W) (surplus := S) (n := n)
    (fun i hi => (hW ⟨i,hi⟩).symm ▸ hw _) (fun i hi j hj hij => by
      rw [hS ⟨i,hi⟩, hS ⟨j,hj⟩]
      exact horder (show (⟨i,hi⟩ : Fin n) ≤ ⟨j,hj⟩ from hij))
    hδ (hm.trans_eq (sum_reindex e hW).symm)
  obtain ⟨hnorm, hbound, hcommon, hgood⟩ := data
  let p (v : V) := pivotProbability W δ (e.symm v)
  let top := univ.filter (fun v : V => (e.symm v).val ∈ feedbackSet W δ n)
  refine ⟨p, top, ?_, ?_, ?_, ?_⟩
  · rw [← hnorm]
    exact (sum_reindex e (fun i => by simp only [p, Equiv.symm_apply_apply])).symm
  · intro v
    simpa only [hW (e.symm v), Equiv.apply_symm_apply] using hbound _ (e.symm v).isLt
  · apply hcommon.trans_eq
    calc
      ∑ i ∈ feedbackSet W δ n, W i =
          ∑ i ∈ range n, if i ∈ feedbackSet W δ n then W i else 0 := by
        rw [← sum_filter]
        congr 1
        ext i
        simp only [feedbackSet, mem_filter, mem_range]
        tauto
      _ = ∑ v ∈ top, w v := by
        rw [sum_filter]
        apply sum_reindex e
        intro i
        simp only [hW, Equiv.symm_apply_apply]
  · intro v hp
    obtain ⟨ha, hb⟩ := hgood _ (e.symm v).isLt hp
    constructor
    · rw [sum_filter] at ha ⊢
      apply lt_of_eq_of_lt _ ha
      symm
      apply sum_reindex e
      intro i
      simp only [hS, hW, Equiv.apply_symm_apply]
    · intro j hj
      have hmj : (e.symm j).val ∈ feedbackSet W δ n := (mem_filter.mp hj).2
      simpa only [hS, Equiv.apply_symm_apply] using hb _ hmj

/-- Quantile pivot distribution on all the active vertices. Only positive surpluses
can be chosen or enter the common feedback band; both statements hold at ties. -/
theorem positive_surplus_pivots {V : Type*} [Fintype V] [DecidableEq V]
    (w score : V → K) {δ : K} (hw : ∀ v, 0 ≤ w v) (hδ : 0 < δ)
    (hm : δ ≤ ∑ v ∈ univ.filter (fun v => 0 < score v), w v) :
    ∃ (p : V → K) (top : Finset V),
      ∑ v, p v = 1 ∧ (∀ v, 0 ≤ p v ∧ p v ≤ 2 * w v / δ) ∧
      δ / 2 ≤ ∑ v ∈ top, w v ∧ (∀ j ∈ top, 0 < score j) ∧
      ∀ v, 0 < p v → 0 < score v ∧
        (∑ j ∈ univ.filter (fun j => score v < score j), w j) < δ ∧
        ∀ j ∈ top, score v ≤ score j := by
  classical
  let u (v : V) := if 0 < score v then w v else 0
  have hu (v : V) : 0 ≤ u v := by dsimp [u]; split <;> simp [*]
  have hle (v : V) : u v ≤ w v := by dsimp [u]; split <;> simp [*]
  rw [sum_filter] at hm
  obtain ⟨p, top, hp, hb, hmass, ht⟩ := exists_quantile_pivots u score hu hδ hm
  refine ⟨p, top.filter (fun j => 0 < score j), hp, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hb i).1, (hb i).2.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hle i) (by norm_num)) hδ.le)⟩
  · rwa [sum_filter]
  · intro j hj
    exact (mem_filter.mp hj).2
  · intro i hpi
    have hi : 0 < score i := by
      by_contra! hn
      have hupper := (hb i).2
      simp [u, not_lt_of_ge hn] at hupper
      exact (not_le_of_gt hpi) hupper
    obtain ⟨hadm, htop⟩ := ht i hpi
    refine ⟨hi, ?_, fun j hj => htop _ (mem_filter.mp hj).1⟩
    apply lt_of_eq_of_lt _ hadm
    apply sum_congr rfl
    intro j hj
    simp [u, hi.trans (mem_filter.mp hj).2]

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
