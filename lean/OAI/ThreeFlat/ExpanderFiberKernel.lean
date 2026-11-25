import OAI.ThreeFlat.ExpanderBasic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

namespace OAI
/-! # Copies of a transition matrix on the fibers of a rank-one projection -/

namespace ThreeFlat.Expander
open Finset

variable {A B T I X : Type*} [Fintype A] [Fintype B] [Fintype T] [Fintype I]

theorem avg_comm (f : A → B → ℝ) :
    avg (fun a => avg (f a)) = avg (fun b => avg (fun a => f a b)) := by
  simp only [avg, ← sum_div]
  rw [Finset.sum_comm]
  ring

theorem avg_sum (f : A → B → ℝ) : avg (fun a => ∑ b, f a b) = ∑ b, avg (fun a => f a b) := by
  unfold avg
  rw [← sum_div, Finset.sum_comm]

/-- A copy of the base matrix acts on the first index of each fiber.
Different second indices have no connecting edges. -/
noncomputable def fiberKernel (e : A ≃ B × T) (G : Matrix B B ℝ) : Matrix A A ℝ := by
  classical
  exact fun i j => if (e i).2 = (e j).2 then G (e i).1 (e j).1 else 0

omit [Fintype A] [Fintype B] [Fintype T] in
theorem fiberKernel_nonneg (e : A ≃ B × T) {G : Matrix B B ℝ}
    (h : ∀ i j, 0 ≤ G i j) (i j : A) : 0 ≤ fiberKernel e G i j := by
  classical
  unfold fiberKernel
  split_ifs <;> simp [h]

omit [Fintype A] [Fintype B] [Fintype T] in
theorem fiberKernel_symm (e : A ≃ B × T) {G : Matrix B B ℝ}
    (h : ∀ i j, G i j = G j i) (i j : A) : fiberKernel e G i j = fiberKernel e G j i := by
  classical
  by_cases he : (e i).2 = (e j).2
  · simp [fiberKernel, he, h (e i).1 (e j).1]
  · simp [fiberKernel, he, Ne.symm he]

theorem fiberKernel_row_cost (e : A ≃ B × T) (G : Matrix B B ℝ) (f : A → ℝ) (i : A) :
    ∑ j, fiberKernel e G i j * f j =
      ∑ b, G (e i).1 b * f (e.symm (b, (e i).2)) := by
  classical
  rw [← e.symm.sum_comp (fun j => fiberKernel e G i j * f j), Fintype.sum_prod_type]
  simp [fiberKernel, ite_mul, eq_comm]

theorem fiberKernel_stochastic (e : A ≃ B × T) {G : Matrix B B ℝ}
    (h : ∀ i, ∑ j, G i j = 1) (i : A) : ∑ j, fiberKernel e G i j = 1 := by
  simpa [h] using fiberKernel_row_cost e G (fun _ => 1) i

omit [Fintype T] in
/-- Reindexing onto the fibers preserves the maximum number of entries in a row. -/
theorem fiberKernel_sparse (e : A ≃ B × T) (G : Matrix B B ℝ) {s : ℕ}
    (hg : ∀ i, (univ.filter fun j => G i j ≠ 0).card ≤ s) (i : A) :
    (univ.filter fun j => fiberKernel e G i j ≠ 0).card ≤ s := by
  classical
  let u := univ.filter fun j => fiberKernel e G i j ≠ 0
  have mem {j} (hj : j ∈ u) : (e i).2 = (e j).2 ∧ G (e i).1 (e j).1 ≠ 0 := by
    have hm := (mem_filter.mp hj).2
    by_cases he : (e i).2 = (e j).2
    · exact ⟨he, by simpa [fiberKernel, he] using hm⟩
    · simp [fiberKernel, he] at hm
  calc
    u.card ≤ (univ.filter fun b => G (e i).1 b ≠ 0).card := by
      apply Finset.card_le_card_of_injOn (fun j => (e j).1)
      · intro j hj
        exact mem_filter.mpr ⟨mem_univ _, (mem hj).2⟩
      · intro j hj k hk he
        exact e.injective (Prod.ext he ((mem hj).1.symm.trans (mem hk).1))
    _ ≤ s := hg _

theorem fiberKernel_energy [PseudoMetricSpace X] (e : A ≃ B × T) (G : Matrix B B ℝ)
    (x : A → X) : energy (fiberKernel e G) x =
      avg (fun t => energy G (fun b => x (e.symm (b,t)))) := by
  unfold energy
  rw [← avg_equiv e.symm]
  simp only [Function.comp_def, fiberKernel_row_cost, Equiv.apply_symm_apply]
  rw [avg_prod (fun (b : B) (t : T) => ∑ j, G b j * dist (x (e.symm (b,t))) (x (e.symm (j,t)))^2), avg_comm]

/-- Mixing a finite collection of fiber layouts at uniformly random choices. -/
noncomputable def fiberMixture (e : I → A ≃ B × T) (G : Matrix B B ℝ) : Matrix A A ℝ :=
  fun i j => avg (fun k => fiberKernel (e k) G i j)

omit [Fintype A] [Fintype B] [Fintype T] in
theorem fiberMixture_nonneg (e : I → A ≃ B × T) {G : Matrix B B ℝ}
    (h : ∀ i j, 0 ≤ G i j) (i j : A) : 0 ≤ fiberMixture e G i j :=
  avg_nonneg fun _ => fiberKernel_nonneg _ h i j

omit [Fintype A] [Fintype B] [Fintype T] in
theorem fiberMixture_symm (e : I → A ≃ B × T) {G : Matrix B B ℝ}
    (h : ∀ i j, G i j = G j i) (i j : A) : fiberMixture e G i j = fiberMixture e G j i :=
  avg_congr _ _ fun _ => fiberKernel_symm _ h i j

theorem fiberMixture_stochastic [Nonempty I] (e : I → A ≃ B × T) {G : Matrix B B ℝ}
    (h : ∀ i, ∑ j, G i j = 1) (i : A) : ∑ j, fiberMixture e G i j = 1 := by
  unfold fiberMixture
  rw [← avg_sum]
  simp only [fiberKernel_stochastic _ h, avg_const]

omit [Fintype T] in
theorem fiberMixture_sparse (e : I → A ≃ B × T) (G : Matrix B B ℝ) {s : ℕ}
    (h : ∀ i, (univ.filter fun j => G i j ≠ 0).card ≤ s) (i : A) :
    (univ.filter fun j => fiberMixture e G i j ≠ 0).card ≤ Fintype.card I * s := by
  classical
  let S (k : I) := univ.filter fun j => fiberKernel (e k) G i j ≠ 0
  have incl : (univ.filter fun j => fiberMixture e G i j ≠ 0) ⊆ univ.biUnion S := by
    intro j hj
    by_contra hnot
    have hz (k : I) : fiberKernel (e k) G i j = 0 := by
      by_contra hn
      exact hnot (mem_biUnion.mpr ⟨k,mem_univ _,mem_filter.mpr ⟨mem_univ _,hn⟩⟩)
    exact (mem_filter.mp hj).2 (by simp [fiberMixture, avg, hz])
  calc
    _ ≤ _ := card_le_card incl
    _ ≤ ∑ k, (S k).card := card_biUnion_le
    _ ≤ ∑ _ : I, s := sum_le_sum fun k _ => fiberKernel_sparse (e k) G h i
    _ = _ := by simp

theorem fiberMixture_energy [PseudoMetricSpace X] (e : I → A ≃ B × T) (G : Matrix B B ℝ)
    (x : A → X) : energy (fiberMixture e G) x =
      avg (fun k => avg (fun t => energy G (fun b => x ((e k).symm (b,t))))) := by
  calc
    _ = avg (fun k => energy (fiberKernel (e k) G) x) := by
      unfold energy fiberMixture
      have mul_avg (q : ℝ) (f : I → ℝ) : avg f * q = avg (fun k => f k * q) := by
        simpa only [mul_comm _ q] using (avg_mul q f).symm
      simp_rw [mul_avg, ← avg_sum]
      exact avg_comm _
    _ = _ := avg_congr _ _ fun k => fiberKernel_energy (e k) G x

/-- One non-linear spectral gap for the three-dimensional matrix configuration
lifts the base graph's Poincaré estimate to the graph of random fiber layouts. -/
theorem Bound.fiberMixture [PseudoMetricSpace X] (e : I → A ≃ B × T) {G : Matrix B B ℝ}
    {α γ : ℝ} (hα : 0 ≤ α) (hG : Bound G X γ)
    (hframe : ∀ x : A → X, variance x ≤ α *
      avg (fun k => avg (fun t => variance (fun b => x ((e k).symm (b,t)))))) :
    Bound (fiberMixture e G) X (α * γ) := by
  intro x
  rw [fiberMixture_energy, mul_assoc, ← avg_mul]
  apply (hframe x).trans
  apply mul_le_mul_of_nonneg_left _ hα
  apply avg_le
  intro k
  rw [← avg_mul]
  exact avg_le fun t => hG _

end ThreeFlat.Expander

end OAI
