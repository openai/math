import OAI.ThreeFlat.ExpanderCesaroMatrix
import OAI.ThreeFlat.ExpanderCloudWalkCount
import OAI.ThreeFlat.ExpanderCloudAverage

namespace OAI
/-! # The integer arc table for a Cesàro step

Multiplying the lazy transition matrix by twice the degree gives an
integer arc matrix. Powers count walks with multiplicity. Rescaling all
powers to the denominator at time `t` and averaging gives the port table.
-/

namespace ThreeFlat.Expander

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The arc table of the lazy walk includes one holding arc per outgoing arc. -/
private def lazyArcs (c : V → V → ℕ) (b : ℕ) : Matrix V V ℕ :=
  fun i j => (if i = j then b else 0) + c i j

private theorem lazyStep_pow_entry (c : V → V → ℕ) {b : ℕ} (hb : 0 < b)
    (k : ℕ) (u v : V) :
    (lazyStep (transition c b) ^ k) u v =
      (1 / ((2 * b : ℕ) : ℝ)) ^ k * (((lazyArcs c b) ^ k) u v : ℝ) := by
  let B := lazyArcs c b
  have heq : lazyStep (transition c b) =
      (1 / ((2 * b : ℕ) : ℝ)) • B.map (Nat.castRingHom ℝ) := by
    ext i j
    have hbr : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    by_cases hij : i = j <;>
      simp [B, lazyArcs, lazyStep, transition, hij, Matrix.map_apply] <;>
      field_simp
  rw [heq, smul_pow, ← Matrix.map_pow, Matrix.smul_apply, smul_eq_mul]
  rfl

/-- With a common multiple of all walk denominators as the number of ports,
the averaged lazy walk is the normalized transition of an integer regular
symmetric arc table. -/
theorem exists_cesaro_arc_table (c : V → V → ℕ) {b t q : ℕ}
    (hb : 0 < b) (ht : 0 < t) (hq : 0 < q)
    (hs : ∀ u v, c u v = c v u) (hr : ∀ u, ∑ v, c u v = b)
    (hd : t * (2*b)^t ∣ q) :
    ∃ a : V → V → ℕ, (∀ u v, a u v = a v u) ∧ (∀ u, ∑ v, a u v = q) ∧
      transition a q = cesaro (lazyStep (transition c b)) t := by
  let r := 2 * b
  let d := t * r ^ t
  let B := lazyArcs c b
  let w (k : ℕ) := r ^ (t - (k+1))
  let total (u v : V) := ∑ k ∈ range t, w k * (B ^ (k+1)) u v
  let a (u v : V) := (q / d) * total u v
  have hrpos : 0 < r := Nat.mul_pos (by decide) hb
  have hdpos : 0 < d := Nat.mul_pos ht (pow_pos hrpos _)
  have hsB (u v : V) : B u v = B v u := by simp only [B, lazyArcs, hs u v, (eq_comm : u = v ↔ v = u)]
  have hrB (u : V) : ∑ v, B u v = r := by simp [B, lazyArcs, sum_add_distrib, hr u, r, two_mul]
  have hdegrees (u : V) : ∑ v, total u v = d := by
    unfold total
    rw [sum_comm]
    calc
      _ = ∑ k ∈ range t, r ^ t := by
        apply sum_congr rfl
        intro k hk
        rw [← mul_sum, nat_walk_rowsum B r hrB]
        dsimp only [w]
        rw [← pow_add, Nat.sub_add_cancel (mem_range.mp hk)]
      _ = d := by simp [d]
  refine ⟨a, ?_, ?_, ?_⟩
  · intro u v
    dsimp only [a, total]
    congr 1
    apply sum_congr rfl
    intro k _
    rw [nat_walk_symm B hsB (k+1) u v]
  · intro u
    simp only [a, ← mul_sum, hdegrees]
    exact Nat.div_mul_cancel (show d ∣ q from hd)
  · ext u v
    have hscaled := cloudAverage_dvd hq hdpos hd
    change ((q / d * total u v : ℕ) : ℝ) / (q : ℝ) = _
    calc
      _ = (1 / (d : ℝ)) * (total u v : ℝ) := by
        rw [Nat.cast_mul, ← hscaled]
        ring
      _ = ∑ k ∈ range t, (1 / (d : ℝ)) * ((w k : ℝ) * ((B^(k+1)) u v : ℝ)) := by
        simp [total, mul_sum]
      _ = ∑ k ∈ range t, (1 / (t : ℝ)) * ((lazyStep (transition c b))^(k+1)) u v := by
        apply sum_congr rfl
        intro k hk
        rw [lazyStep_pow_entry c hb, ← mul_assoc, ← mul_assoc]
        congr 1
        simpa only [d, Nat.cast_mul, Nat.cast_pow, w, r] using
          (cloudAverage_weight (b := r) hrpos ht (mem_range.mp hk))
      _ = _ := by
        simp [cesaro, Matrix.sum_apply, mul_sum]

end ThreeFlat.Expander

end OAI
