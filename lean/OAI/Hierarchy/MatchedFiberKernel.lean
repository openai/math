import OAI.ThreeFlat.ExpanderFiberKernel
import Mathlib.Tactic.Linarith

namespace OAI
/-! # Sparse kernels for paired partitions of a finite vertex set

Two endpoint partitions of each Grassmann adjacency have equally large
fibers. The bijection matching their local coordinates gives one permutation
of the vertex set. Combine its symmetric walk with the old walk on the
first endpoint's fibers.
-/

noncomputable section
namespace Hierarchy.NonlinearExpanders

open Finset Matrix ThreeFlat.Expander
open scoped Classical

variable {A B T J X : Type*} [Fintype A] [Fintype B] [Fintype T] [Fintype J]
variable [Nonempty J] [Nonempty B]

/-- The independent-pair energy on conditional fibers of the two endpoints. -/
def pairedEnergy [PseudoMetricSpace X] (e f : J → A ≃ B × T) (x : A → X) : ℝ :=
  avg fun j => avg fun t => avg fun a => avg fun b =>
    dist (x ((e j).symm (a,t))) (x ((f j).symm (b,t)))^2

private def permRow (p : Equiv.Perm A) (a b : A) : ℝ := if p a = b then 1 else 0

private def permWalk (p : Equiv.Perm A) (a b : A) : ℝ :=
  (permRow p a b + permRow p.symm a b)/2

omit [Fintype A] in
private theorem permWalk_sym (p : Equiv.Perm A) (a b : A) : permWalk p a b = permWalk p b a := by
  have h (u v : A) : p.symm u = v ↔ p v = u := by
    rw [Equiv.symm_apply_eq]; exact eq_comm
  simp only [permWalk, permRow, h, add_comm (if p a = b then (1:ℝ) else 0)]

omit [Fintype A] in
private theorem permWalk_nonneg (p : Equiv.Perm A) (a b : A) : 0 ≤ permWalk p a b := by
  unfold permWalk permRow
  split_ifs <;> norm_num

private theorem permWalk_row (p : Equiv.Perm A) (a : A) : ∑ b, permWalk p a b = 1 := by
  simp [permWalk, permRow, ← sum_div, sum_add_distrib]

private theorem permWalk_energy [PseudoMetricSpace X] (p : Equiv.Perm A) (x : A → X) :
    energy (permWalk p) x = avg fun a => dist (x a) (x (p a))^2 := by
  let d (a : A) := dist (x a) (x (p a))^2
  have rev (a : A) : dist (x a) (x (p.symm a))^2 = (d ∘ p.symm) a := by
    simp [d, dist_comm]
  unfold energy
  have row (a : A) : (∑ b, permWalk p a b * dist (x a) (x b)^2) =
      (d a + (d ∘ p.symm) a)/2 := by
    simp only [permWalk, div_mul_eq_mul_div, add_mul, ← sum_div, sum_add_distrib,
      permRow, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true, rev, d]
  simp_rw [row, div_eq_inv_mul, avg_mul, avg_add, avg_equiv p.symm]
  ring

private def mate (e f : A ≃ B × T) : A ≃ A := e.trans f.symm

private def walks (e f : J → A ≃ B × T) (G : Matrix B B ℝ) (a b : ℝ)
    (i : J) (x y : A) : ℝ :=
  (a * fiberKernel (e i) G x y + b * permWalk (mate (e i) (f i)) x y) / (a+b)

/-- Average the matched permutation and the intra-fiber walk with weights
that give the desired two terms of the quadratic bound. -/
def matchedKernel (e f : J → A ≃ B × T) (G : Matrix B B ℝ) (a b : ℝ) : Matrix A A ℝ :=
  fun x y => avg fun i => walks e f G a b i x y

omit [Fintype B] [Fintype T] [Nonempty J] [Nonempty B] [Fintype A] in
theorem matchedKernel_symm (e f : J → A ≃ B × T) {G : Matrix B B ℝ}
    (sym : ∀ a b, G a b = G b a) (v w : ℝ) (x y : A) :
    matchedKernel e f G v w x y = matchedKernel e f G v w y x := by
  exact avg_congr _ _ fun i => by simp only [walks, fiberKernel_symm _ sym x y, permWalk_sym _ x y]

omit [Nonempty B] in
theorem matchedKernel_row [DecidableEq A] [DecidableEq B] (e f : J → A ≃ B × T) {G : Matrix B B ℝ}
    (row : G ∈ rowStochastic ℝ B) {v w : ℝ} (hv : 0 ≤ v) (hw : 0 < w) :
    matchedKernel e f G v w ∈ rowStochastic ℝ A := by
  obtain ⟨hG, hsum⟩ := mem_rowStochastic_iff_sum.mp row
  have hp : 0 < v+w := by linarith
  apply mem_rowStochastic_iff_sum.mpr
  constructor
  · intro x y
    exact avg_nonneg fun i => div_nonneg (add_nonneg
      (mul_nonneg hv (fiberKernel_nonneg _ hG x y))
      (mul_nonneg hw.le (permWalk_nonneg _ x y))) hp.le
  · intro x
    unfold matchedKernel
    rw [← avg_sum]
    simp only [walks, ← sum_div, sum_add_distrib, ← mul_sum, permWalk_row,
      fiberKernel_stochastic _ hsum, mul_one, div_self hp.ne', avg_const]

omit [Fintype T] [Nonempty B] in
theorem matchedKernel_sparse (e f : J → A ≃ B × T) {G : Matrix B B ℝ} {s : ℕ}
    (supp : ∀ i, (univ.filter fun j => G i j ≠ 0).card ≤ s)
    (v w : ℝ) (x : A) :
    (univ.filter fun y => matchedKernel e f G v w x y ≠ 0).card ≤
      Fintype.card J * (s+2) := by
  classical
  let U (i : J) := univ.filter fun y => fiberKernel (e i) G x y ≠ 0
  let P (i : J) := mate (e i) (f i)
  let S (i : J) := insert (P i x) (insert ((P i).symm x) (U i))
  have hsub : (univ.filter fun y => matchedKernel e f G v w x y ≠ 0) ⊆ univ.biUnion S := by
    intro y hy
    by_contra hn
    have hz (i : J) : walks e f G v w i x y = 0 := by
      have nh : y ∉ S i := fun h => hn (mem_biUnion.mpr ⟨i,mem_univ _,h⟩)
      have nmem : y ≠ P i x ∧ y ≠ (P i).symm x ∧ fiberKernel (e i) G x y = 0 := by
        simpa [S,U] using nh
      simp [walks,permWalk,permRow,← show P i = mate (e i) (f i) from rfl,
        Ne.symm nmem.1, Ne.symm nmem.2.1,nmem.2.2]
    exact (mem_filter.mp hy).2 (by simp [matchedKernel,hz])
  have hsize (i : J) : (S i).card ≤ s+2 := by
    have h1 := card_insert_le (P i x) (insert ((P i).symm x) (U i))
    have h2 := card_insert_le ((P i).symm x) (U i)
    have h3 : (U i).card ≤ s := fiberKernel_sparse (e i) G supp x
    dsimp [S]
    omega
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ i, (S i).card := card_biUnion_le
    _ ≤ ∑ _ : J, (s+2) := sum_le_sum fun i _ => hsize i
    _ = _ := by simp


private theorem dist_sq_weighted [PseudoMetricSpace X] (x y z : X) {ε : ℝ} (pos : 0 < ε) :
    dist x z ^ 2 ≤ (1+ε)*dist x y ^ 2 + (1+1/ε)*dist y z ^ 2 := by
  calc
    _ ≤ (dist x y + dist y z)^2 := by
      exact pow_le_pow_left₀ dist_nonneg (dist_triangle x y z) _
    _ ≤ _ := by
      field_simp
      nlinarith [sq_nonneg (ε*dist x y - dist y z)]

omit [Nonempty B] in
private theorem matchEnergy [PseudoMetricSpace X] (e f : A ≃ B × T) (x : A → X) :
    energy (permWalk (mate e f)) x =
      avg fun t => avg fun b => dist (x (e.symm (b,t))) (x (f.symm (b,t)))^2 := by
  rw [permWalk_energy]
  calc
    _ = avg ((fun a => dist (x a) (x (mate e f a))^2) ∘ e.symm) :=
      (avg_equiv e.symm _).symm
    _ = avg (fun b => avg fun t => dist (x (e.symm (b,t))) (x (f.symm (b,t)))^2) := by
      simpa only [Function.comp_def, mate, Equiv.trans_apply, Equiv.apply_symm_apply]
        using (avg_prod (fun b t => dist (x (e.symm (b,t))) (x (f.symm (b,t)))^2))
    _ = _ := avg_comm _

omit [Fintype B] [Fintype T] [Fintype J] [Nonempty J] [Nonempty B] in
private theorem walks_energy [PseudoMetricSpace X] (e f : J → A ≃ B × T)
    (G : Matrix B B ℝ) (v w : ℝ) (i : J) (x : A → X) :
    energy (walks e f G v w i) x = (v+w)⁻¹ *
      (v*energy (fiberKernel (e i) G) x + w*energy (permWalk (mate (e i) (f i))) x) := by
  let H := fiberKernel (e i) G
  let P := permWalk (mate (e i) (f i))
  have split (a b : A) :
      walks e f G v w i a b * dist (x a) (x b)^2 =
      (v+w)⁻¹ * (v*(H a b * dist (x a) (x b)^2) + w*(P a b * dist (x a) (x b)^2)) := by
    unfold walks H P
    ring
  unfold energy
  simp_rw [split, ← mul_sum, sum_add_distrib, ← mul_sum, avg_mul, avg_add, avg_mul]; rfl

omit [Fintype B] [Fintype T] [Nonempty J] [Nonempty B] in
private theorem energy_matchedKernel [PseudoMetricSpace X] (e f : J → A ≃ B × T)
    (G : Matrix B B ℝ) (v w : ℝ) (x : A → X) :
    energy (matchedKernel e f G v w) x = (v+w)⁻¹ * avg (fun i =>
      v*energy (fiberKernel (e i) G) x + w*energy (permWalk (mate (e i) (f i))) x) := by
  calc
    _ = avg fun i => energy (walks e f G v w i) x := by
      unfold matchedKernel energy
      have mul_avg (q : ℝ) (g : J → ℝ) : avg g * q = avg (fun j => g j * q) := by
        simpa only [mul_comm _ q] using (avg_mul q g).symm
      simp_rw [mul_avg, ← avg_sum]
      exact avg_comm _
    _ = _ := by simp only [walks_energy, avg_mul]

omit [Nonempty J] in
/-- A paired-fiber Poincaré inequality is preserved by the new stochastic
matrix, with an additive constant for the fiber matching. -/
theorem bound_matchedKernel [PseudoMetricSpace X] (e f : J → A ≃ B × T)
    {G : Matrix B B ℝ} {γ β ε : ℝ} (hγ : 0 ≤ γ) (hβ : 0 ≤ β) (hε : 0 < ε)
    (old : Bound G X γ) (frame : ∀ x : A → X, variance x ≤ β * pairedEnergy e f x) :
    Bound (matchedKernel e f G ((1+ε)*γ) (1+1/ε)) X
      (β*((1+ε)*γ + (1+1/ε))) := by
  intro x
  let v := (1+ε)*γ
  let w := 1+1/ε
  have pos : 0 < v+w := by dsimp [v,w]; positivity
  have step (u z : B → X) :
      (avg fun a => avg fun b => dist (u a) (z b)^2) ≤
      v * energy G u + w * (avg fun b => dist (u b) (z b)^2) := by
    calc
      _ ≤ avg fun a => avg fun b =>
          (1+ε)*dist (u a) (u b)^2 + w*dist (u b) (z b)^2 :=
        avg_le fun a => avg_le fun b => dist_sq_weighted _ _ _ hε
      _ = (1+ε)*variance u + w*(avg fun b => dist (u b) (z b)^2) := by
        simp only [avg_add,avg_mul,avg_const,variance]
      _ ≤ _ := by
        apply add_le_add_left
        change (1+ε)*variance u ≤ ((1+ε)*γ)*energy G u
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (old u) (by positivity)
  have localBound (i : J) :
      (avg fun t => avg fun a => avg fun b =>
        dist (x ((e i).symm (a,t))) (x ((f i).symm (b,t)))^2) ≤
      v*energy (fiberKernel (e i) G) x + w*energy (permWalk (mate (e i) (f i))) x := by
    rw [fiberKernel_energy, matchEnergy, ←avg_mul, ←avg_mul, ←avg_add]
    exact avg_le fun t => step (fun a => x ((e i).symm (a,t))) (fun a => x ((f i).symm (a,t)))
  apply (frame x).trans
  change β * pairedEnergy e f x ≤ (β*(v+w)) * energy (matchedKernel e f G v w) x
  rw [energy_matchedKernel, mul_assoc, ←mul_assoc (v+w), mul_inv_cancel₀ pos.ne', one_mul]
  exact mul_le_mul_of_nonneg_left (avg_le localBound) hβ

end Hierarchy.NonlinearExpanders

end
end OAI
