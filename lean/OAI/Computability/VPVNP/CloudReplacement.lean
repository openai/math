import OAI.Computability.VPVNP.WalkEnergy
import Mathlib.Data.Fintype.BigOperators

/-!
# Cloud replacement in the bounded-degree amplification

Section 5.3 of *VP and VNP differ over every field* replaces each old vertex
with a copy of a fixed port graph. Half the steps stay in the cloud and half
follow a matching on the ports. The matching realizes an averaged walk on the
old vertices. The estimates below use the same normalization as `walkEnergy`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

open scoped BigOperators

variable {V K X : Type*} [Fintype V] [Fintype K] [PseudoMetricSpace X]

private theorem sq_dist_le_three_segments (a b c d : X) :
    dist a d ^ 2 ≤ 3 * (dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2) := by
  have h := (dist_triangle a b d).trans (add_le_add_right (dist_triangle b c d) _)
  have hs := pow_le_pow_left₀ dist_nonneg h 2
  nlinarith [sq_nonneg (dist a b - dist b c), sq_nonneg (dist b c - dist c d),
    sq_nonneg (dist c d - dist a b)]

/-- The energy between the centers of matched clouds is bounded by the matching energy
and twice the squared displacement to a port's center (§5.3). -/
theorem cloudMatchingEnergy_le (σ : Equiv.Perm (V × K)) (x : V × K → X) (y : V → X) :
    (∑ p : V × K, dist (y p.1) (y (σ p).1) ^ 2) ≤
      3 * (2 * (∑ p : V × K, dist (x p) (y p.1) ^ 2) +
        ∑ p : V × K, dist (x p) (x (σ p)) ^ 2) := by
  calc
    _ ≤ ∑ p : V × K, 3 * (dist (x p) (y p.1) ^ 2 + dist (x p) (x (σ p)) ^ 2 +
        dist (x (σ p)) (y (σ p).1) ^ 2) := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [dist_comm (y p.1) (x p)] using
        sq_dist_le_three_segments (y p.1) (x p) (x (σ p)) (y (σ p).1)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Equiv.sum_comp σ (fun p : V × K => dist (x p) (y p.1) ^ 2)]
      ring

/-- The transition matrix on clouds obtained by following a matching from a
uniformly chosen port. -/
noncomputable def portWalk [DecidableEq V] (σ : Equiv.Perm (V × K)) : Matrix V V ℝ :=
  fun v w ↦ ((Finset.univ.filter (fun k : K ↦ (σ (v, k)).1 = w)).card : ℝ) /
    Fintype.card K

/-- The internal transition kernel and the matching transition each have weight one half. -/
noncomputable def cloudWalk [DecidableEq V] [DecidableEq K]
    (H : Matrix K K ℝ) (σ : Equiv.Perm (V × K)) : Matrix (V × K) (V × K) ℝ :=
  fun p q ↦ ((if p.1 = q.1 then H p.2 q.2 else 0) + (if σ p = q then 1 else 0)) / 2

private theorem cloudWalk_energy [DecidableEq V] [DecidableEq K]
    (H : Matrix K K ℝ) (σ : Equiv.Perm (V × K)) (x : V × K → X) :
    walkEnergy (cloudWalk H σ) x =
      ((∑ v, walkEnergy H (fun k ↦ x (v,k))) + ∑ p, dist (x p) (x (σ p)) ^ 2) / 2 := by
  have row (p : V × K) :
      (∑ q : V × K, (if p.1 = q.1 then H p.2 q.2 else 0) * dist (x q) (x p) ^ 2) =
      ∑ k, H p.2 k * dist (x (p.1, k)) (x p) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp
  simp only [walkEnergy, cloudWalk, div_mul_eq_mul_div]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  congr 1
  simp only [add_mul, Finset.sum_add_distrib, row]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  · rw [Fintype.sum_prod_type]
  · exact Finset.sum_congr rfl fun p _ ↦ by rw [dist_comm]

private theorem portWalk_energy [DecidableEq V] [Nonempty K]
    (σ : Equiv.Perm (V × K)) (y : V → X) :
    (Fintype.card K : ℝ) * walkEnergy (portWalk σ) y =
      ∑ p, dist (y p.1) (y (σ p).1) ^ 2 := by
  have hK : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [walkEnergy, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  have term (w : V) : (Fintype.card K : ℝ) * (portWalk σ v w * dist (y w) (y v) ^ 2) =
      ∑ k : K, if (σ (v, k)).1 = w then dist (y v) (y w) ^ 2 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, portWalk, dist_comm (y w) (y v)]
    field_simp
  simp_rw [term]
  rw [Finset.sum_comm]
  simp

private theorem cloudCenters [Nonempty K] (H : Matrix K K ℝ)
    {β : ℝ} (hH : HasPoincareBound X H β) (x : V × K → X) :
    ∃ y : V → X, (∑ p : V × K, dist (x p) (y p.1) ^ 2) ≤
      β * ∑ v, walkEnergy H (fun k ↦ x (v,k)) := by
  have hK : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have each (v : V) : ∃ k : K, (∑ l : K, dist (x (v,l)) (x (v,k)) ^ 2) ≤
        β * walkEnergy H (fun l ↦ x (v,l)) := by
    have hbound := (div_le_iff₀ hK).mp (hH (fun l ↦ x (v,l)))
    rw [Finset.sum_comm] at hbound
    have hs : (∑ k : K, ∑ l : K, dist (x (v,l)) (x (v,k)) ^ 2) ≤
        ∑ _k : K, β * walkEnergy H (fun l ↦ x (v,l)) := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_comm (Fintype.card K : ℝ)] using hbound
    obtain ⟨k, _, hk⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
    exact ⟨k, hk⟩
  choose k hk using each
  refine ⟨fun v ↦ x (v,k v), ?_⟩
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ ↦ hk v

private theorem lifted_pair_sum (y : V → X) :
    (∑ p : V × K, ∑ q : V × K, dist (y p.1) (y q.1) ^ 2) =
      (Fintype.card K : ℝ) ^ 2 * ∑ i : V, ∑ j : V, dist (y i) (y j) ^ 2 := by
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- The cloud graph amplifies a bound on the induced walk between clouds
using the bound on the internal port graph. -/
theorem cloudWalk_hasPoincareBound [DecidableEq V] [DecidableEq K] [Nonempty V] [Nonempty K]
    (H : Matrix K K ℝ) (σ : Equiv.Perm (V × K))
    {β δ : ℝ} (hβ : 1 ≤ β) (hδ : 0 ≤ δ) (hH : HasPoincareBound X H β)
    (hS : HasPoincareBound X (portWalk σ) δ) :
    HasPoincareBound X (cloudWalk H σ) (12 * β * (1 + 3 * δ)) := by
  intro x
  obtain ⟨y, hy⟩ := cloudCenters H hH x
  let I := ∑ v, walkEnergy H (fun k ↦ x (v,k))
  let M := ∑ p, dist (x p) (x (σ p)) ^ 2
  let D := ∑ p : V × K, dist (x p) (y p.1) ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun p _ ↦ sq_nonneg _
  have hD : D ≤ β * I := hy
  have hV : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hK : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hcomp := pairVariance_le_displacement_variance x (fun p : V × K ↦ y p.1)
  simp only [lifted_pair_sum, Fintype.card_prod, Nat.cast_mul] at hcomp
  have hsmall := (div_le_iff₀ hV).mp (hS y)
  have hmatch := cloudMatchingEnergy_le σ x y
  rw [← portWalk_energy] at hmatch
  change (Fintype.card K : ℝ) * walkEnergy (portWalk σ) y ≤ 3 * (2 * D + M) at hmatch
  have hmacro :
      (Fintype.card K : ℝ) ^ 2 * (∑ i, ∑ j, dist (y i) (y j) ^ 2) ≤
        (Fintype.card V : ℝ) * Fintype.card K * (δ * (3 * (2 * D + M))) := by
    calc
      _ ≤ (Fintype.card K : ℝ) ^ 2 *
          ((δ * walkEnergy (portWalk σ) y) * Fintype.card V) :=
        mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
      _ = ((Fintype.card V : ℝ) * Fintype.card K * δ) *
          ((Fintype.card K : ℝ) * walkEnergy (portWalk σ) y) := by ring
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left hmatch (mul_nonneg (mul_nonneg hV.le hK.le) hδ) using 1
        ring
  have coeff : 3 * (2 * D + δ * (3 * (2 * D + M))) ≤
      12 * β * (1 + 3 * δ) * ((I + M) / 2) := by
    have hD' := mul_le_mul_of_nonneg_left hD (show 0 ≤ 6 + 18 * δ by linarith)
    have hc : 9 * δ ≤ 6 * β + 18 * β * δ := by
      nlinarith only [hβ, hδ, mul_nonneg (sub_nonneg.mpr hβ) hδ]
    nlinarith only [hD', mul_le_mul_of_nonneg_right hc hM]
  rw [cloudWalk_energy, Fintype.card_prod, Nat.cast_mul]
  apply (div_le_iff₀ (mul_pos hV hK)).mpr
  change _ ≤ _ * ((I + M) / 2) * ((Fintype.card V : ℝ) * Fintype.card K)
  calc
    _ ≤ 3 * (2 * ((Fintype.card V : ℝ) * Fintype.card K) * D +
        (Fintype.card K : ℝ) ^ 2 * (∑ i, ∑ j, dist (y i) (y j) ^ 2)) := hcomp
    _ ≤ 3 * (2 * ((Fintype.card V : ℝ) * Fintype.card K) * D +
        (Fintype.card V : ℝ) * Fintype.card K * (δ * (3 * (2 * D + M)))) := by linarith only [hmacro]
    _ = (3 * (2 * D + δ * (3 * (2 * D + M)))) *
        ((Fintype.card V : ℝ) * Fintype.card K) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coeff (mul_nonneg hV.le hK.le)

end SpectralGeometry

end VPVNP
end Computability
end OAI
