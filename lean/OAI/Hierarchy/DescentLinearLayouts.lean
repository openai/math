import OAI.Hierarchy.DescentGLFiber
import OAI.Hierarchy.DescentBaseVariance

namespace OAI
/-! # Uniform invertible layouts for dyadic base reservation -/

namespace Hierarchy.DescentLinearLayouts

open DescentGL DescentBaseVariance
open scoped Classical
noncomputable section

variable {k j : ℕ}

def layout (hj : j≤k) (L : Layout k) (x : Bits k) : Bits j := headRows hj (L x)

/-- Uniformly random invertible row systems send a fixed nonzero difference to
each nonzero vector equally often. The fraction reaching the prefix kernel
therefore has this exact value. -/
theorem collision_exact (hj : j≤k) (x y : Bits k) (ne : x≠y) :
    collision (layout hj) x y = ((2^(k-j)-1 : ℕ):ℝ) / ((2^k-1 : ℕ):ℝ) := by
  have hk : k≠0 := by
    rintro rfl
    exact ne (Subsingleton.elim x y)
  have power : 1<(2:ℕ)^k := Nat.one_lt_pow (by omega) (by decide)
  have nonzero : 0<(2:ℕ)^k-1 := by omega
  have pos : 0<Fintype.card (Layout k) := Fintype.card_pos_iff.mpr ⟨LinearEquiv.refl _ _⟩
  unfold collision layout
  apply (div_eq_div_iff (by exact_mod_cast pos.ne') (by exact_mod_cast nonzero.ne')).2
  norm_cast
  convert! prefix_collision_count hj x y ne using 2; congr!

/-- The pairwise collision bound required by the weighted base-variance estimate. -/
theorem pairBound (k j : ℕ) (hj : j≤k) : PairBound (layout hj) := by
  intro x y ne
  rw [collision_exact hj x y ne,card_bits]
  have hk : k≠0 := by
    rintro rfl
    exact ne (Subsingleton.elim x y)
  have power : 1<(2:ℕ)^k := Nat.one_lt_pow (by omega) (by decide)
  have nonzero : 0<(2:ℕ)^k-1 := by omega
  apply (div_le_div_iff₀ (by exact_mod_cast nonzero) (by positivity)).2
  rw [one_mul]
  have bound : (2^(k-j)-1)*2^j ≤ (2:ℕ)^k-1 := by
    rw [Nat.sub_mul,one_mul,←pow_add,Nat.sub_add_cancel hj]
    have := Nat.two_pow_pos j
    omega
  exact_mod_cast bound

end
end Hierarchy.DescentLinearLayouts

end OAI
