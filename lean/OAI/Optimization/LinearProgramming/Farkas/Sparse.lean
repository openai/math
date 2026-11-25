import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.SplitIfs

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Farkas

variable {K : Type*}

open Finset Module
open scoped BigOperators Matrix

variable {K ι E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Eliminate a linear dependence among the active generators of a nonnegative sum. -/
private theorem reduce_nonneg_sum [AddCommGroup E] [Module K E]
    (v : ι → E) (c : ι → K)
    (hdir : ∀ (s : Finset ι), ¬LinearIndepOn K v (s : Set ι) →
      ∃ g : ι → K, (∑ i ∈ s, g i • v i) = 0 ∧ 0 ≤ ∑ i ∈ s, g i * c i ∧
        ∃ k ∈ s, 0 < g k)
    (s : Finset ι) (w : ι → K) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ (t : Finset ι) (z : ι → K), t ⊆ s ∧ LinearIndepOn K v (t : Set ι) ∧
      (∀ i ∈ t, 0 ≤ z i) ∧ (∑ i ∈ t, z i • v i) = ∑ i ∈ s, w i • v i ∧
      ∑ i ∈ t, z i * c i ≤ ∑ i ∈ s, w i * c i := by
  classical
  induction s using Finset.strongInductionOn generalizing w with | _ s ih =>
  by_cases hind : LinearIndepOn K v (s : Set ι)
  · exact ⟨s, w, Subset.rfl, hind, hw, rfl, le_rfl⟩
  obtain ⟨g, hgz, hgc, k, hks, hk⟩ := hdir s hind
  let pos := s.filter fun i => 0 < g i
  obtain ⟨p, hp, hpmin⟩ := pos.exists_min_image (fun i => w i / g i)
    ⟨k, mem_filter.mpr ⟨hks, hk⟩⟩
  obtain ⟨hps, hpg⟩ := mem_filter.mp hp
  let a := w p / g p
  let w' := fun i => w i - a * g i
  have ha : 0 ≤ a := div_nonneg (hw p hps) hpg.le
  have hw' : ∀ i ∈ s, 0 ≤ w' i := by
    intro i hi
    apply sub_nonneg.mpr
    by_cases hgi : 0 < g i
    · exact (le_div_iff₀ hgi).mp (hpmin i (mem_filter.mpr ⟨hi, hgi⟩))
    · exact (mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt hgi)).trans (hw i hi)
  have hpzero : w' p = 0 := by simp [w', a, hpg.ne']
  have heq : ∑ i ∈ s.erase p, w' i • v i = ∑ i ∈ s, w i • v i := by
    rw [sum_erase (f := fun i => w' i • v i) s (by simp [hpzero])]
    simp only [w', sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, hgz, smul_zero, sub_zero]
  have hcost : ∑ i ∈ s.erase p, w' i * c i ≤ ∑ i ∈ s, w i * c i := by
    rw [sum_erase (f := fun i => w' i * c i) s (by simp [hpzero])]
    simp only [w', sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
    exact sub_le_self _ (mul_nonneg ha hgc)
  obtain ⟨t, z, ht, hi, hz, hrep, hle⟩ := ih (s.erase p) (erase_ssubset hps) w'
    (fun i hi => hw' i (mem_of_mem_erase hi))
  exact ⟨t, z, ht.trans (erase_subset p s), hi, hz, hrep.trans heq, hle.trans hcost⟩

/-- Preserve a nonnegative sum on a linearly independent subset of its generators. -/
theorem independent_nonneg_sum_supported [Fintype ι] [AddCommGroup E] [Module K E]
    (v : ι → E) (w : ι → K) (hw : ∀ i, 0 ≤ w i) :
    ∃ z : ι → K, (∀ i, 0 ≤ z i) ∧ (∑ i, z i • v i) = ∑ i, w i • v i ∧
      LinearIndepOn K v (Function.support z) ∧ Function.support z ⊆ Function.support w := by
  classical
  have dir (s : Finset ι) (h : ¬LinearIndepOn K v (s : Set ι)) :
      ∃ g : ι → K, (∑ i ∈ s, g i • v i) = 0 ∧
        0 ≤ (∑ i ∈ s, g i * (0 : K)) ∧ ∃ k ∈ s, 0 < g k := by
    obtain ⟨u, hu, j, hj, hne⟩ := not_linearIndepOn_finset_iff.mp h
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact ⟨fun i => -u i, by simp [neg_smul, hu], by simp, j, hj, neg_pos.mpr hneg⟩
    · exact ⟨u, hu, by simp, j, hj, hpos⟩
  let S := univ.filter fun i => w i ≠ 0
  obtain ⟨t, z, htS, hind, hz, hrep, _⟩ := reduce_nonneg_sum v (fun _ => 0) dir S w
    (fun i _ => hw i)
  have hfull : (∑ i ∈ S, w i • v i) = ∑ i, w i • v i :=
    sum_filter_of_ne fun i _ hi hwz => hi (by simp [hwz])
  let z' := fun i => if i ∈ t then z i else 0
  have hsum : (∑ i, z' i • v i) = ∑ i ∈ t, z i • v i := by
    simp [z', ite_smul]
  have hsub : Function.support z' ⊆ (t : Set ι) := by
    intro i hi
    by_contra ht
    change i ∉ t at ht
    exact hi (by simp [z', ht])
  exact ⟨z', fun i => by dsimp [z']; split_ifs with hi; exacts [hz i hi, le_rfl],
    hsum.trans (hrep.trans hfull), hind.mono hsub,
    fun _ hi => (mem_filter.mp (htS (hsub hi))).2⟩

theorem independent_nonneg_sum [Fintype ι] [AddCommGroup E] [Module K E]
    (v : ι → E) (w : ι → K) (hw : ∀ i, 0 ≤ w i) :
    ∃ z : ι → K, (∀ i, 0 ≤ z i) ∧ (∑ i, z i • v i) = ∑ i, w i • v i ∧
      LinearIndepOn K v (Function.support z) := by
  obtain ⟨z, hz, he, hi, _⟩ := independent_nonneg_sum_supported v w hw
  exact ⟨z, hz, he, hi⟩

/-- A conic combination in finite dimension needs at most as many generators as the dimension. -/
theorem sparse_nonneg_sum_supported [Fintype ι] [AddCommGroup E] [Module K E] [Module.Finite K E]
    (v : ι → E) (w : ι → K) (hw : ∀ i, 0 ≤ w i) :
    ∃ z : ι → K, (∀ i, 0 ≤ z i) ∧ (∑ i, z i • v i) = ∑ i, w i • v i ∧
      (univ.filter fun i => z i ≠ 0).card ≤ finrank K E ∧ Function.support z ⊆ Function.support w := by
  classical
  obtain ⟨z, hz, hsum, hind, hsup⟩ := independent_nonneg_sum_supported v w hw
  let t := univ.filter fun i => z i ≠ 0
  have h : LinearIndepOn K v (t : Set ι) := by simpa [t, Function.support] using hind
  exact ⟨z, hz, hsum, by simpa using h.fintype_card_le_finrank, hsup⟩

theorem sparse_nonneg_sum [Fintype ι] [AddCommGroup E] [Module K E] [Module.Finite K E]
    (v : ι → E) (w : ι → K) (hw : ∀ i, 0 ≤ w i) :
    ∃ z : ι → K, (∀ i, 0 ≤ z i) ∧ (∑ i, z i • v i) = ∑ i, w i • v i ∧
      (univ.filter fun i => z i ≠ 0).card ≤ finrank K E := by
  obtain ⟨z, hz, he, hc, _⟩ := sparse_nonneg_sum_supported v w hw
  exact ⟨z, hz, he, hc⟩

/-- Compress normalized nonnegative weights without increasing a linear objective. The augmented
rows on the retained support are linearly independent. -/
theorem convex_sparse_min [Fintype ι] [AddCommGroup E] [Module K E]
    (H : ι → E) (c w : ι → K) (hw : ∀ i, 0 ≤ w i) :
    ∃ (t : Finset ι) (z : ι → K), LinearIndepOn K (fun i => (H i, (1 : K))) (t : Set ι) ∧
      (∀ i ∈ t, 0 ≤ z i) ∧ (∑ i ∈ t, z i • H i) = ∑ i, w i • H i ∧
      (∑ i ∈ t, z i) = ∑ i, w i ∧ (∑ i ∈ t, z i * c i) ≤ ∑ i, w i * c i := by
  classical
  let v := fun i => (H i, (1 : K))
  have dir (s : Finset ι) (h : ¬LinearIndepOn K v (s : Set ι)) :
      ∃ g : ι → K, (∑ i ∈ s, g i • v i) = 0 ∧
        0 ≤ (∑ i ∈ s, g i * c i) ∧ ∃ k ∈ s, 0 < g k := by
    obtain ⟨u, hu, j, hj, hne⟩ := not_linearIndepOn_finset_iff.mp h
    have hu0 : ∑ i ∈ s, u i = 0 := by
      simpa [v, Prod.snd_sum] using congrArg Prod.snd hu
    by_cases hc : 0 ≤ ∑ i ∈ s, u i * c i
    · exact ⟨u, hu, hc, exists_pos_of_sum_zero_of_exists_nonzero u hu0 ⟨j, hj, hne⟩⟩
    · refine ⟨fun i => -u i, by simp [neg_smul, hu], by simpa using (neg_nonneg.mpr (le_of_not_ge hc)), ?_⟩
      apply exists_pos_of_sum_zero_of_exists_nonzero (fun i => -u i) (by simp [hu0])
      exact ⟨j, hj, neg_ne_zero.mpr hne⟩
  obtain ⟨t, z, _, hind, hz, hrep, hle⟩ := reduce_nonneg_sum v c dir univ w (fun i _ => hw i)
  exact ⟨t, z, hind, hz, by simpa [v, Prod.fst_sum] using congrArg Prod.fst hrep,
    by simpa [v, Prod.snd_sum] using congrArg Prod.snd hrep, hle⟩

/-- A Farkas certificate can be normalized to `bᵀ z = -1` and supported on at most
`rank A + 1` rows, over the original ordered coefficient field. -/
theorem sparse_certificate_supported {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b y : Fin m → K)
    (hy : 0 ≤ y) (hA : Aᵀ.mulVec y = 0) (hb : dotProduct b y < 0) :
    ∃ z : Fin m → K, 0 ≤ z ∧ Aᵀ.mulVec z = 0 ∧ dotProduct b z = -1 ∧
      (univ.filter fun i => z i ≠ 0).card ≤ A.rank + 1 ∧ Function.support z ⊆ Function.support y := by
  classical
  let W := Submodule.span K (Set.range A.row)
  let row (i : Fin m) : W := ⟨A.row i, Submodule.subset_span ⟨i, rfl⟩⟩
  let v (i : Fin m) := (row i, b i)
  let scale := (-dotProduct b y)⁻¹
  have hscale : 0 ≤ scale := (inv_pos.mpr (neg_pos.mpr hb)).le
  let w : Fin m → K := scale • y
  have hw (i : Fin m) : 0 ≤ w i := mul_nonneg hscale (hy i)
  have hAw : Aᵀ.mulVec w = 0 := by simp [w, Matrix.mulVec_smul, hA]
  have hbw : dotProduct b w = -1 := by
    rw [show w = scale • y from rfl, dotProduct_smul]
    simp [scale, hb.ne]
  obtain ⟨z, hz, hrep, hcard, hsupp⟩ := sparse_nonneg_sum_supported v w hw
  refine ⟨z, hz, ?_, ?_, ?_, ?_⟩
  · funext j
    let f : W × K →ₗ[K] K := (LinearMap.proj j).comp (W.subtype.comp (LinearMap.fst K W K))
    have h := congrArg f hrep
    simp only [map_sum, map_smul, smul_eq_mul] at h
    change (∑ i, z i * A i j) = ∑ i, w i * A i j at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h.trans (by
      simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hAw j)
  · have h := congrArg (LinearMap.snd K W K) hrep
    simp only [map_sum, map_smul, smul_eq_mul] at h
    change (∑ i, z i * b i) = ∑ i, w i * b i at h
    simpa [dotProduct, mul_comm] using h.trans (by simpa [dotProduct, mul_comm] using hbw)
  · simpa [Module.finrank_prod, W, ← Matrix.rank_eq_finrank_span_row] using hcard

  · intro i hi hzero
    exact hsupp hi (by simp [w, hzero])

theorem sparse_certificate {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b y : Fin m → K)
    (hy : 0 ≤ y) (hA : Aᵀ.mulVec y = 0) (hb : dotProduct b y < 0) :
    ∃ z : Fin m → K, 0 ≤ z ∧ Aᵀ.mulVec z = 0 ∧ dotProduct b z = -1 ∧
      (univ.filter fun i => z i ≠ 0).card ≤ A.rank + 1 := by
  obtain ⟨z, hz, hA', hb', hc, _⟩ := sparse_certificate_supported A b y hy hA hb
  exact ⟨z, hz, hA', hb', hc⟩

end Farkas
end LinearProgramming
end Optimization
end OAI
