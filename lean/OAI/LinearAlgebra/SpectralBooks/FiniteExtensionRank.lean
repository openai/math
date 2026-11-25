import OAI.LinearAlgebra.SpectralBooks.RankLimit
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Tensor rank under finite scalar extension

Expand two sites of a decomposition in a fixed basis of the extension.
A linear retraction of the field inclusion contracts the third site.
The dimension cost is constant across tensor powers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation Filter
open scoped Topology

section

variable {F K X Y Z : Type*} [Field F] [Field K] [Algebra F K]

/-- Kronecker powers commute with entrywise scalar extension. -/
theorem power_scalarExtension (T : Tensor F X Y Z) (n : ℕ) :
    Tensor.power (fun x y z => algebraMap F K (T x y z)) n =
      fun x y z => algebraMap F K (Tensor.power T n x y z) := by
  funext x y z
  simp [Tensor.power]

/-- A finite extension of degree `d` saves at most a factor of `d²` in tensor rank. -/
theorem rankAtMost_of_finiteExtension [FiniteDimensional F K] {T : Tensor F X Y Z}
    {r : ℕ} (h : Tensor.RankAtMost (fun x y z => algebraMap F K (T x y z)) r) :
    Tensor.RankAtMost T (r * (Module.finrank F K) ^ 2) := by
  classical
  let d := Module.finrank F K
  let b := Module.finBasis F K
  obtain ⟨P, hP⟩ := (Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F K))
  obtain ⟨A, B, C, hABC⟩ := h
  let a (j : Fin r × Fin d × Fin d) (x : X) := b.repr (A j.1 x) j.2.1
  let a' (j : Fin r × Fin d × Fin d) (y : Y) := b.repr (B j.1 y) j.2.2
  let c (j : Fin r × Fin d × Fin d) (z : Z) := P (b j.2.1 * b j.2.2 * C j.1 z)
  have hterm (i : Fin r) (x : X) (y : Y) (z : Z) :
      P (Tensor.rankOne (A i) (B i) (C i) x y z) =
      ∑ j : Fin d, ∑ k : Fin d, Tensor.rankOne (a (i,j,k)) (a' (i,j,k)) (c (i,j,k)) x y z := by
    unfold Tensor.rankOne
    conv_lhs => rw [← b.sum_repr (A i x), ← b.sum_repr (B i y)]
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum, a, a', c,
      smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [mul_left_comm]
    rfl
  have heq : T = fun x y z => ∑ j, Tensor.rankOne (a j) (a' j) (c j) x y z := by
    funext x y z
    have he := LinearMap.congr_fun hP (T x y z)
    change P (algebraMap F K (T x y z)) = T x y z at he
    rw [← he, congrFun (congrFun (congrFun hABC x) y) z, map_sum]
    simp only [Fintype.sum_prod_type, hterm]
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin, sq, d] using
    Tensor.rankAtMost_sum_rankOne a a' c

variable [Fintype X] [Fintype Y]

/-- A constant factor in a tensor-power rank bound disappears under roots. -/
theorem asymptoticRank_le_of_power_bound (T : Tensor F X Y Z) {C r : ℕ}
    (hC : 0 < C) (h : ∀ n : ℕ, tensorRank (Tensor.power T n) ≤ C * r ^ n) :
    asymptoticRank T ≤ r := by
  have hc : Tendsto (fun n : ℕ => (C : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hcont := Real.continuousAt_const_rpow (a := (C : ℝ)) (b := 0) (by positivity)
    simpa only [Real.rpow_zero, Function.comp_def] using
      hcont.tendsto.comp (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hlim := hc.mul_const (r : ℝ)
  rw [one_mul] at hlim
  apply le_of_tendsto_of_tendsto (tendsto_tensorRank_power_root T) hlim
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  calc
    (tensorRank (Tensor.power T n) : ℝ) ^ ((n : ℝ)⁻¹) ≤
        ((C : ℝ) * (r : ℝ) ^ n) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast h n) (by positivity)
    _ = (C : ℝ) ^ ((n : ℝ)⁻¹) * r := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.pow_rpow_inv_natCast (by positivity) hn]

/-- Any exact decomposition over a finite extension bounds the asymptotic rank
over the original field. -/
theorem asymptoticRank_le_of_finiteExtension [FiniteDimensional F K] {T : Tensor F X Y Z}
    {r : ℕ} (h : Tensor.RankAtMost (fun x y z => algebraMap F K (T x y z)) r) :
    asymptoticRank T ≤ r := by
  apply asymptoticRank_le_of_power_bound T (C := (Module.finrank F K) ^ 2)
    (pow_pos Module.finrank_pos 2)
  intro n
  have hpow := h.power n
  rw [power_scalarExtension] at hpow
  simpa only [mul_comm] using tensorRank_le_of_rankAtMost (rankAtMost_of_finiteExtension hpow)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
