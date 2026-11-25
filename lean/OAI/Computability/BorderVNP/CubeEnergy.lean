import OAI.Computability.VPVNP.GrassmannGeometry
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Antipodal distance on the binary cube

Lemma 8.1 uses Enflo's inequality for maps of the binary cube into a CAT(0) space.
Averaging the squared quadrilateral inequality over translations bounds the cost of
all antipodal pairs by the largest cost of an edge times the square root of the dimension.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

open VPVNP.SpectralGeometry

/-- The binary cube with coordinatewise addition modulo two. -/
abbrev Vertex (a : ℕ) := Fin a → ZMod 2

/-- Toggle just the given coordinate. -/
def step {a : ℕ} (i : Fin a) : Vertex a := Pi.single i 1

/-- The endpoint of an antipodal pair whose first bit is zero. -/
def start {n : ℕ} (x : Vertex n) : Vertex (n + 1) := Fin.cons 0 x

/-- The other endpoint of the same pair. -/
def stop {n : ℕ} (x : Vertex n) : Vertex (n + 1) := start x + 1

private theorem sum_translate {a : ℕ} (f : Vertex a → ℝ) (u : Vertex a) :
    (∑ x, f (x + u)) = ∑ x, f x := Equiv.sum_comp (Equiv.addRight u) f

variable {X : Type*} [PseudoMetricSpace X]

/-- The sum of squared distances at displacement `u`. -/
noncomputable def energy {a : ℕ} (f : Vertex a → X) (u : Vertex a) : ℝ :=
  ∑ x, dist (f x) (f (x + u)) ^ 2

/-- Adding two displacements increases their squared-distance sum by at most
the sum of their individual squared-distance sums. -/
theorem energy_add_le {a : ℕ} (hc : HasCATZeroSegments X) (f : Vertex a → X)
    (u v : Vertex a) : energy f (u + v) ≤ energy f u + energy f v := by
  let D (x y : Vertex a) := dist (f x) (f y) ^ 2
  have hsym x y : D x y = D y x := by simp only [D, dist_comm (f x) (f y)]
  have cancel (x y : Vertex a) : x + y + y = x := by
    ext i; exact CharTwo.add_cancel_right (R := ZMod 2) _ _
  have trans (w u : Vertex a) :
      (∑ x, D (x + w) (x + w + u)) = energy f u :=
    sum_translate (fun x ↦ D x (x + u)) w
  have diag (x : Vertex a) : x + u + (u + v) = x + v := by rw [← add_assoc, cancel]
  have opp (x : Vertex a) : D (x + u + v) (x + v) = D (x + v) (x + v + u) := by
    rw [hsym]; congr 1; abel
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦
    quadrilateral_sq hc (f x) (f (x + u)) (f (x + u + v)) (f (x + v)))
  change (∑ x, (D x (x + u + v) + D (x + u) (x + v))) ≤
    ∑ x, (D x (x + u) + D (x + u) (x + u + v) + D (x + u + v) (x + v) + D (x + v) x) at h
  simp only [Finset.sum_add_distrib, opp, trans] at h
  have hdiag : (∑ x, D (x + u) (x + v)) = energy f (u + v) := by
    simpa only [diag] using trans u (u + v)
  have side : (∑ x, D (x + v) x) = energy f v := by
    exact Finset.sum_congr rfl (fun x _ ↦ hsym (x + v) x)
  rw [hdiag, side] at h
  simp only [add_assoc] at h
  change energy f (u + v) + energy f (u + v) ≤
    energy f u + (energy f v + (energy f u + energy f v)) at h
  linarith

/-- Full antipodal energy is bounded by the sum of the coordinate energies. -/
theorem energy_antipode_le {a : ℕ} (hc : HasCATZeroSegments X) (f : Vertex a → X) :
    energy f 1 ≤ ∑ i : Fin a, energy f (step i) := by
  classical
  have bound (s : Finset (Fin a)) :
      energy f (∑ i ∈ s, step i) ≤ ∑ i ∈ s, energy f (step i) := by
    induction s using Finset.induction_on with
    | empty => simp [energy]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (energy_add_le hc f _ _).trans (add_le_add_right ih _)
  have hs : (∑ i : Fin a, step i) = 1 := by
    change (∑ i : Fin a, Pi.single i ((1 : Vertex a) i)) = (1 : Vertex a)
    exact Finset.univ_sum_single 1
  exact hs ▸ bound Finset.univ

private theorem cons_flip {n : ℕ} (z : ZMod 2) (x : Vertex n) :
    Fin.cons z x + (1 : Vertex (n+1)) = Fin.cons (z+1) (x+1) := by
  ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

private theorem sum_half {n : ℕ} (f : Vertex (n + 1) → X) :
    energy f 1 = 2 * ∑ x : Vertex n, dist (f (start x)) (f (stop x)) ^ 2 := by
  unfold energy
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ ZMod 2)).sum_comp,
    Fintype.sum_prod_type]
  change (∑ i : Fin 2, ∑ x : Vertex n, dist (f (Fin.cons (i : ZMod 2) x))
    (f (Fin.cons (i : ZMod 2) x + 1)) ^ 2) = _
  rw [Fin.sum_univ_two]
  have flip (x : Vertex n) : dist (f (Fin.cons (1 : ZMod 2) x))
      (f (Fin.cons (1 : ZMod 2) x + 1)) =
      dist (f (start (x+1))) (f (stop (x+1))) := by
    have hx : x + 1 + 1 = x := by ext i; exact CharTwo.add_cancel_right (R := ZMod 2) _ _
    simp only [start, stop, cons_flip, zero_add, hx, CharTwo.add_self_eq_zero]
    exact dist_comm _ _
  change (∑ x : Vertex n, dist (f (start x)) (f (stop x)) ^ 2) +
    (∑ x : Vertex n, dist (f (Fin.cons 1 x)) (f (Fin.cons 1 x + 1)) ^ 2) = _
  simp_rw [flip]
  rw [sum_translate (fun x ↦ dist (f (start x)) (f (stop x)) ^ 2) 1]
  ring

/-- The cost of the `2^n` undirected antipodal pairs in dimension `n+1` is at most
`2^n * sqrt (n+1)` times an upper bound for the cost of each cube edge. -/
theorem antipodal_distance_le (n : ℕ) (hc : HasCATZeroSegments X)
    (f : Vertex (n + 1) → X) {m : ℝ} (hm : 0 ≤ m)
    (he : ∀ x i, dist (f x) (f (x + step i)) ≤ m) :
    (∑ x : Vertex n, dist (f (start x)) (f (stop x))) ≤
      2 ^ n * Real.sqrt (n+1) * m := by
  have count (k : ℕ) : Fintype.card (Vertex k) = 2 ^ k := by
    simp [Vertex, ZMod.card]
  have bound (i : Fin (n+1)) : energy f (step i) ≤ 2^(n+1) * m^2 := by
    calc
      _ ≤ ∑ _x : Vertex (n+1), m^2 :=
        Finset.sum_le_sum fun x _ ↦ (sq_le_sq₀ dist_nonneg hm).mpr (he x i)
      _ = _ := by simp [count]
  have henergy := (energy_antipode_le hc f).trans (Finset.sum_le_sum (fun i _ ↦ bound i))
  rw [sum_half] at henergy
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, pow_succ (2 : ℝ) n] at henergy
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Vertex n ↦ (1 : ℝ)) (fun x ↦ dist (f (start x)) (f (stop x)))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, count, nsmul_eq_mul,
    mul_one, Nat.cast_pow, Nat.cast_ofNat] at hcauchy
  apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ ↦ dist_nonneg) (by positivity)).mp
  calc
    _ ≤ _ := hcauchy
    _ ≤ 2^n * ((n+1) * 2^n * m^2) := by gcongr; linarith only [henergy]
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring

end Cube

end BorderVNP
end Computability
end OAI
