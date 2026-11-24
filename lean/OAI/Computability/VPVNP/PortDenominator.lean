import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FieldSimp

/-!
# Integral multiplicities of a lazy Cesàro walk

In Section 5.3 of *VP and VNP differ over every field*, the normalized
adjacency matrix of a symmetric `b`-regular multigraph is made lazy and its
first `t` positive powers are averaged. To realize this matrix on `Q` ports
per vertex, multiply each entry by `Q`. The resulting natural counts are
obtained from walks in the original multigraph with `b` extra loops at each
vertex. The proof works over both the rationals and the reals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem sum_pow_row (B : Matrix V V ℕ) {d : ℕ} (hB : ∀ u, ∑ v, B u v = d)
    (h : ℕ) (u : V) : ∑ v, (B ^ h) u v = d ^ h := by
  induction h with
  | zero => simp [Matrix.one_apply]
  | succ h ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hB]
    rw [← Finset.sum_mul, ih]

/-- The Section 5.3 lazy transition matrix and its Cesàro average give
symmetric natural port multiplicities with row sums `Q` whenever the common
denominator `t * (2*b)^t` divides `Q`. The rational and real specializations
use the same integer witness. -/
theorem exists_cesaroPortCounts (K : Type*) [Field K] [CharZero K]
    (G : Matrix V V ℕ) {b t Q : ℕ} (hb : 0 < b) (ht : 0 < t)
    (hsym : ∀ u v, G u v = G v u) (hrow : ∀ u, ∑ v, G u v = b)
    (hdiv : t * (2 * b) ^ t ∣ Q) :
    let A : Matrix V V K := fun u v ↦ ((if u = v then 1 else 0) + G u v / (b : K)) / 2
    let S : Matrix V V K := fun u v ↦ (∑ h ∈ Finset.range t, (A ^ (h + 1)) u v) / t
    ∃ a : Matrix V V ℕ, (∀ u v, a u v = a v u) ∧ (∀ u, ∑ v, a u v = Q) ∧
      ∀ u v, (a u v : K) = Q * S u v := by
  intro A S
  obtain ⟨k, rfl⟩ := hdiv
  let d := 2 * b
  let B : Matrix V V ℕ := fun u v ↦ (if u = v then b else 0) + G u v
  have hBrow (u : V) : ∑ v, B u v = d := by simp [B, d, Finset.sum_add_distrib, hrow, two_mul]
  have hBsym : B.IsSymm := Matrix.IsSymm.ext fun u v ↦ by
    simp only [B, hsym v u, @eq_comm _ v u]
  have hpow (h : ℕ) (hl : h ≤ t) : d ^ (t - h) * d ^ h = d ^ t := by
    rw [← pow_add, Nat.sub_add_cancel hl]
  let a : Matrix V V ℕ := fun u v ↦ k * ∑ h ∈ Finset.range t,
    d ^ (t - (h + 1)) * (B ^ (h + 1)) u v
  refine ⟨a, ?_, ?_, ?_⟩
  · intro u v
    dsimp only [a]
    congr 1
    exact Finset.sum_congr rfl fun h _ ↦ congrArg _ ((hBsym.pow _).apply v u)
  · intro u
    dsimp only [a]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_pow_row B hBrow]
    rw [Finset.sum_congr rfl (fun h hh ↦ hpow (h + 1) (Finset.mem_range.mp hh))]
    simp [d, mul_comm k]
  · have hbK : (b : K) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    have htK : (t : K) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
    have hmap : B.map (Nat.castRingHom K) = (d : K) • A := by
      ext u v
      change (((if u = v then b else 0) + G u v : ℕ) : K) =
        ((2 * b : ℕ) : K) * (((if u = v then 1 else 0) + G u v / (b : K)) / 2)
      split_ifs <;> push_cast <;> field_simp
      simp
    have hcast (h : ℕ) (u v : V) : ((B ^ h) u v : K) = (d : K) ^ h * (A ^ h) u v := by
      change ((B ^ h).map (Nat.castRingHom K)) u v = _
      rw [Matrix.map_pow, hmap, smul_pow, Matrix.smul_apply, smul_eq_mul]
    intro u v
    dsimp only [a, S]
    push_cast
    simp_rw [hcast, ← mul_assoc]
    have hpowK (h : ℕ) (hh : h ∈ Finset.range t) :
        (d : K) ^ (t - (h + 1)) * (d : K) ^ (h + 1) = (d : K) ^ t := by
      rw [← pow_add, Nat.sub_add_cancel (Finset.mem_range.mp hh)]
    rw [Finset.sum_congr rfl (fun h hh ↦ congrArg (· * (A ^ (h + 1)) u v) (hpowK h hh)),
      ← Finset.mul_sum]
    simp only [d, Nat.cast_mul, Nat.cast_ofNat]
    field_simp

end SpectralGeometry

end VPVNP
end Computability
end OAI
