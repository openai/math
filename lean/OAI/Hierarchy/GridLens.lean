import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace OAI
/-! # Euclidean rail lengths in the lens estimate

A rail crosses all cells of one coordinate line of the grid with centers
spaced three units apart. Each cell passage joins the two unit translates
of its center. Only the links to the two foci move in transverse directions.
-/

namespace Hierarchy.GridLens
open scoped BigOperators
noncomputable section

variable {k : ℕ}

/-- The point on the line with transverse coordinates `z` and longitudinal coordinate `a`. -/
def point (j : Fin k) (z : Fin k → ℝ) (a : ℝ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => if i = j then a else z i)

@[simp] theorem point_apply (i j : Fin k) (z : Fin k → ℝ) (a : ℝ) :
    point j z a i = if i = j then a else z i := rfl

theorem dist_sq (j : Fin k) (z z' : Fin k → ℝ) (a b : ℝ) :
    dist (point j z a) (point j z' b) ^ 2 =
      (a-b)^2 + ∑ i ∈ Finset.univ.erase j, (z i-z' i)^2 := by
  rw [EuclideanSpace.dist_sq_eq]
  rw [← Finset.add_sum_erase (a := j) _ _ (Finset.mem_univ j)]
  congr 1
  · simp [Real.dist_eq]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [Real.dist_eq, (Finset.mem_erase.mp hi).1]

theorem dist_along (j : Fin k) (z : Fin k → ℝ) (a b : ℝ) (hab : a ≤ b) :
    dist (point j z a) (point j z b) = b-a := by
  apply (sq_eq_sq₀ dist_nonneg (sub_nonneg.mpr hab)).mp
  rw [dist_sq]
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero]
  ring

/-- End-link bound for a longitudinal difference `a` of at least `R/2`. -/
private theorem end_excess {length a R energy : ℝ} (hR : 0 < R)
    (ha : R ≤ 2*a) (hE : 0 ≤ energy) (len : length^2 ≤ a^2+energy) :
    length ≤ a+energy/R := by
  have a0 : 0 ≤ a := by linarith
  have e0 := div_nonneg hE hR.le
  have h := mul_le_mul_of_nonneg_right ha e0
  have cancel : R*(energy/R) = energy := by
    rw [mul_comm,div_mul_cancel₀ _ hR.ne']
  rw [cancel] at h
  apply le_of_sq_le_sq _ (add_nonneg a0 e0)
  nlinarith [sq_nonneg (energy/R)]

/-- A coordinate of one of the grid centers belongs to `{3,6,…,3(n+1)}`. -/
def center (t : ℕ) : ℝ := 3*((t:ℝ)+1)

private theorem transverse_energy {n : ℕ} (j : Fin k) (row : Fin k → Fin (n+1)) :
    (∑ i ∈ Finset.univ.erase j, (center (row i).val)^2) ≤
      ((k-1:ℕ):ℝ)*9*((n:ℝ)+1)^2 := by
  calc
    _ ≤ ∑ _i ∈ Finset.univ.erase j, (3*((n:ℝ)+1))^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hnat : (row i).val ≤ n := Nat.le_of_lt_succ (row i).isLt
      have h : ((row i).val:ℝ) ≤ n := by exact_mod_cast hnat
      have lo : 0 ≤ center (row i).val := by unfold center; positivity
      have hi : center (row i).val ≤ 3*((n:ℝ)+1) := by unfold center; linarith
      exact pow_le_pow_left₀ lo hi 2
    _ = _ := by simp [Finset.card_erase_of_mem]; ring

/-- Total length from the negative to the positive focus of direction `j`
through all `n+1` cell passages. The second sum traverses the interior links. -/
def railCost {n : ℕ} (j : Fin k) (row : Fin k → Fin (n+1)) (R : ℝ) : ℝ :=
  let z := fun i => center (row i).val
  dist (point j 0 (-R)) (point j z (center 0-1)) +
    (∑ t : Fin (n+1), dist (point j z (center t.val-1)) (point j z (center t.val+1))) +
    (∑ t : Fin n, dist (point j z (center t.val+1)) (point j z (center (t.val+1)-1))) +
    dist (point j z (center n+1)) (point j 0 R)

theorem railCost_le {n : ℕ} (j : Fin k) (row : Fin k → Fin (n+1)) (R : ℝ)
    (far : 8*((n:ℝ)+1) ≤ R) :
    railCost j row R ≤ 2*R + 18*((k-1:ℕ):ℝ)*((n:ℝ)+1)^2/R := by
  let z := fun i => center (row i).val
  let cap : ℝ := ((k-1:ℕ):ℝ)*9*((n:ℝ)+1)^2
  have nn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hR : 0 < R := by linarith
  have c0 : 0 ≤ cap := by dsimp [cap]; positivity
  have left : dist (point j 0 (-R)) (point j z (center 0-1)) ≤ R+2+cap/R := by
    apply end_excess hR (by linarith) c0
    rw [dist_sq]
    simp only [Pi.zero_apply, zero_sub, neg_sq]
    have longitudinal : (-R - (center 0-1))^2 = (R+2)^2 := by norm_num [center]; ring
    rw [longitudinal]
    exact add_le_add le_rfl (transverse_energy j row)
  have right : dist (point j z (center n+1)) (point j 0 R) ≤ R-(center n+1)+cap/R := by
    apply end_excess hR (by unfold center; linarith) c0
    rw [dist_sq]
    simp only [Pi.zero_apply,sub_zero]
    have longitudinal : (center n+1-R)^2 = (R-(center n+1))^2 := by ring
    rw [longitudinal]
    exact add_le_add le_rfl (transverse_energy j row)
  have cell (t : Fin (n+1)) :
      dist (point j z (center t.val-1)) (point j z (center t.val+1)) = 2 := by
    rw [dist_along _ _ _ _ (by linarith)]
    ring
  have link (t : Fin n) :
      dist (point j z (center t.val+1)) (point j z (center (t.val+1)-1)) = 1 := by
    unfold center
    rw [Nat.cast_add,Nat.cast_one,dist_along _ _ _ _ (by linarith)]
    ring
  change dist (point j 0 (-R)) (point j z (center 0-1)) +
    (∑ t : Fin (n+1), dist (point j z (center t.val-1)) (point j z (center t.val+1))) +
    (∑ t : Fin n, dist (point j z (center t.val+1)) (point j z (center (t.val+1)-1))) +
    dist (point j z (center n+1)) (point j 0 R) ≤ _
  simp only [cell,link,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,mul_one]
  calc
    _ ≤ (R+2+cap/R) + ((n:ℝ)+1)*2 + (n:ℝ) + (R-(center n+1)+cap/R) :=
      add_le_add (add_le_add (add_le_add left le_rfl) le_rfl) right
    _ = _ := by unfold cap center; ring

/-- Geometric transport budget of all external rails. Their transverse
coordinates and directions can depend on the individual pair. -/
theorem total_rail_cost_le {n E : ℕ} (direction : Fin E → Fin k)
    (row : Fin E → Fin k → Fin (n+1)) (R : ℝ) (far : 8*((n:ℝ)+1) ≤ R) :
    ∑ e, railCost (direction e) (row e) R ≤
      2*R*E + 18*((k-1:ℕ):ℝ)*E*((n:ℝ)+1)^2/R := by
  calc
    _ ≤ ∑ _e : Fin E, (2*R + 18*((k-1:ℕ):ℝ)*((n:ℝ)+1)^2/R) :=
      Finset.sum_le_sum (fun e _ => railCost_le (direction e) (row e) R far)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring


end
end Hierarchy.GridLens

end OAI
