import OAI.Computability.VPVNP.PortMatching
import OAI.Computability.VPVNP.WalkEnergy
import Mathlib.Algebra.BigOperators.Field

/-!
# Loop removal at bounded Poincaré cost

Section 5.3 of *VP and VNP differ over every field* removes loops from a
regular graph by doubling its vertex set. Each step moves to the opposite
layer, choosing equally between an old edge and a vertical edge.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {V X : Type*} [Fintype V] [DecidableEq V] [PseudoMetricSpace X]

/-- The transition matrix of the loopless double cover. -/
noncomputable def layerWalk (P : Matrix V V ℝ) : Matrix (V × Bool) (V × Bool) ℝ :=
  fun p q ↦ if q.2 = !p.2 then (P p.1 q.1 + (if q.1 = p.1 then 1 else 0)) / 2 else 0

omit [Fintype V] in
/-- Dividing the doubled graph's integer multiplicities by its degree gives
the crossing/vertical transition kernel. -/
theorem layerArcs_normalize (G : V → V → ℕ) {b : ℕ} (hb : 0 < b) (p q : V × Bool) :
    (layerArcs G b p q : ℝ) / (2 * b) =
      layerWalk (fun u v ↦ (G u v : ℝ) / b) p q := by
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  simp only [layerArcs, layerWalk]
  split_ifs <;> push_cast <;> field_simp <;> ring

private noncomputable def crossEnergy (P : Matrix V V ℝ) (x : V × Bool → X) (i : Bool) : ℝ :=
  ∑ v, ∑ w, P v w * dist (x (w, !i)) (x (v, i)) ^ 2

private noncomputable def verticalEnergy (x : V × Bool → X) : ℝ :=
  ∑ v, dist (x (v, true)) (x (v, false)) ^ 2

private theorem layerWalk_energy (P : Matrix V V ℝ) (hs : ∀ u v, P u v = P v u)
    (x : V × Bool → X) :
    walkEnergy (layerWalk P) x = crossEnergy P x false + verticalEnergy x := by
  have hc : crossEnergy P x true = crossEnergy P x false := by
    unfold crossEnergy
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun w _ ↦ by
      simp only [Bool.not_true, Bool.not_false]
      rw [hs w v, dist_comm]
  have row (v : V) (i : Bool) :
      ∑ q, layerWalk P (v, i) q * dist (x q) (x (v, i)) ^ 2 =
        ((∑ w, P v w * dist (x (w, !i)) (x (v, i)) ^ 2) +
          dist (x (v, !i)) (x (v, i)) ^ 2) / 2 := by
    rw [Fintype.sum_prod_type]
    simp only [layerWalk, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      div_mul_eq_mul_div, add_mul, one_mul, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [walkEnergy, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [row, ← Finset.sum_div, Finset.sum_add_distrib]
  simp only [Fintype.sum_bool, Bool.not_true, Bool.not_false]
  rw [show (∑ v, dist (x (v, false)) (x (v, true)) ^ 2) = verticalEnergy x from
    Finset.sum_congr rfl fun v _ ↦ by rw [dist_comm]]
  change (crossEnergy P x true + crossEnergy P x false +
    (verticalEnergy x + verticalEnergy x)) / 2 = _
  rw [hc]
  ring

omit [DecidableEq V] in
private theorem firstLayer_energy_le (P : Matrix V V ℝ) (hn : ∀ v w, 0 ≤ P v w)
    (hcol : ∀ w, ∑ v, P v w = 1) (x : V × Bool → X) :
    walkEnergy P (fun v ↦ x (v, false)) ≤ 2 * (crossEnergy P x false + verticalEnergy x) := by
  have edge (v w : V) :
      dist (x (w, false)) (x (v, false)) ^ 2 ≤
        2 * (dist (x (w, true)) (x (v, false)) ^ 2 + dist (x (w, true)) (x (w, false)) ^ 2) := by
    have h := dist_triangle (x (w, false)) (x (w, true)) (x (v, false))
    rw [dist_comm (x (w, false)) (x (w, true))] at h
    have h' := pow_le_pow_left₀ dist_nonneg h 2
    nlinarith [sq_nonneg (dist (x (w, true)) (x (v, false)) - dist (x (w, true)) (x (w, false)))]
  have hc : (∑ v, ∑ w, P v w * dist (x (w, true)) (x (w, false)) ^ 2) = verticalEnergy x := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, one_mul, verticalEnergy]
  calc
    _ ≤ ∑ v, ∑ w, 2 * (P v w * dist (x (w, true)) (x (v, false)) ^ 2 +
        P v w * dist (x (w, true)) (x (w, false)) ^ 2) := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro w _
      have h := mul_le_mul_of_nonneg_left (edge v w) (hn v w)
      linarith only [h]
    _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib, hc, crossEnergy, Bool.not_false]

/-- The loopless double cover of a symmetric stochastic walk inherits a
uniform Poincaré constant. The estimate applies to every metric target. -/
theorem layerWalk_hasPoincareBound [Nonempty V] (P : Matrix V V ℝ)
    (hn : ∀ v w, 0 ≤ P v w) (hs : ∀ v w, P v w = P w v) (hcol : ∀ w, ∑ v, P v w = 1)
    {γ : ℝ} (hγ : 0 ≤ γ) (hP : HasPoincareBound X P γ) :
    HasPoincareBound X (layerWalk P) (6 + 12 * γ) := by
  intro x
  let y (p : V × Bool) := x (p.1, false)
  have disp : (∑ p, dist (x p) (y p) ^ 2) = verticalEnergy x := by
    rw [Fintype.sum_prod_type]
    simp [y, verticalEnergy]
  have pairs : (∑ p, ∑ q, dist (y p) (y q) ^ 2) =
      4 * (∑ v, ∑ w, dist (x (v, false)) (x (w, false)) ^ 2) := by
    simp only [Fintype.sum_prod_type, y, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
    ring
  have hCard : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hCard' : (Fintype.card (V × Bool) : ℝ) = 2 * Fintype.card V := by
    simp [mul_comm]
  have hvar := pairVariance_le_displacement_variance x y
  rw [disp, pairs, hCard'] at hvar
  have hold := (div_le_iff₀ hCard).mp (hP (fun v ↦ x (v, false)))
  have he := firstLayer_energy_le P hn hcol x
  have hnCross : 0 ≤ crossEnergy P x false :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_nonneg (hn _ _) (sq_nonneg _)
  rw [hCard', layerWalk_energy P hs x]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hvar, hold, mul_nonneg hCard.le hnCross,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hγ) hCard.le]

omit [DecidableEq V] in
/-- A Poincaré inequality for a target with two separated points forces the
support of a symmetric walk to be connected. Test with a two-valued map
constant on every component. -/
theorem reachable_of_poincare (z₀ z₁ : X) (hsep : 0 < dist z₀ z₁) (P : Matrix V V ℝ) (hn : ∀ i j, 0 ≤ P i j)
    (hs : ∀ i j, P i j = P j i) {γ : ℝ} (hP : HasPoincareBound X P γ) (u v : V) :
    Relation.ReflTransGen (fun i j ↦ 0 < P i j) u v := by
  classical
  let reachable := Relation.ReflTransGen (fun i j ↦ 0 < P i j) u
  by_contra hv
  let f (i : V) : X := if reachable i then z₀ else z₁
  have hsame (i j : V) (hij : 0 < P i j) : reachable i ↔ reachable j :=
    ⟨fun h ↦ h.tail hij, fun h ↦ h.tail ((hs i j) ▸ hij)⟩
  have zero (i j : V) : P i j * dist (f j) (f i) ^ 2 = 0 := by
    rcases (hn i j).eq_or_lt with h | h
    · rw [← h, zero_mul]
    · simp [f, hsame i j h]
  have energy : walkEnergy P f = 0 := by simp [walkEnergy, zero]
  have hu : reachable u := .refl
  have hpair : 0 < dist (f u) (f v) ^ 2 := by
    change ¬ reachable v at hv
    simpa [f, hu, hv] using sq_pos_of_pos hsep
  have hp : 0 < ∑ i, ∑ j, dist (f i) (f j) ^ 2 :=
    Finset.sum_pos' (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      ⟨u, Finset.mem_univ u, Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨v, Finset.mem_univ v, hpair⟩⟩
  have : Nonempty V := ⟨u⟩
  have hnCard : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have h := hP f
  rw [energy, mul_zero] at h
  exact (div_pos hp hnCard).not_ge h

end SpectralGeometry

end VPVNP
end Computability
end OAI
