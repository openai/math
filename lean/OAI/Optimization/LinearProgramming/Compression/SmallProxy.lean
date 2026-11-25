import OAI.Optimization.LinearProgramming.Compression.ProxyBounds
import OAI.Optimization.LinearProgramming.Compression.AffineRAMInput

/-! In the all-small branch the sign is obtained from an integer dot product
after clearing the common dyadic denominator. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

def smallProxyLeft {n : ℕ} (D : ℕ) (a : Fin n → ℤ) : Fin (n+1) → ℚ :=
  Fin.cases (D : ℚ) (fun i => (a i : ℚ))

def smallProxyRight {n : ℕ} (c : ℤ) (grid : Fin n → ℤ) : Fin (n+1) → ℚ :=
  Fin.cases (c : ℚ) (fun i => (grid i : ℚ))

theorem smallProxyDot_value {n : ℕ} (D : ℕ) (c : ℤ) (a grid : Fin n → ℤ) :
    dotProduct (smallProxyLeft D a) (smallProxyRight c grid) =
      (clearedProxyOffset ∅ D c a grid : ℚ) := by
  simp [dotProduct, Fin.sum_univ_succ, smallProxyLeft, smallProxyRight, clearedProxyOffset]

theorem smallProxyDot_sign {n : ℕ} (D : ℕ) (hD : 0 < D) (c : ℤ) (a grid : Fin n → ℤ)
    (mag : Fin n → ℚ) :
    let x := dotProduct (smallProxyLeft D a) (smallProxyRight c grid)
    let v := proxyAffine ∅ D c a grid mag
    (if x < 0 then 0 else if 0 < x then 2 else 1 : ℕ) =
      (if v < 0 then 0 else if 0 < v then 2 else 1) := by
  dsimp only
  rw [smallProxyDot_value]
  simp only [Int.cast_lt_zero, Int.cast_pos]
  have h := compareProxyAffine_correct (∅ : Finset (Fin n)) D hD c a grid mag
    (by simp)
  rw [compareProxyAffine, ite_eq_right (by simp)] at h
  change (if clearedProxyOffset ∅ D c a grid < 0 then Ordering.lt
      else if 0 < clearedProxyOffset ∅ D c a grid then .gt else .eq) = _ at h
  split_ifs at h ⊢ <;> rfl

private theorem proxyInt_height {x : ℤ} {H : ℕ} (hH : 1 ≤ H) (h : |x| ≤ (H : ℤ)) :
    (x : ℚ).num.natAbs ≤ H ∧ (x : ℚ).den ≤ H := by
  have hx : (x.natAbs : ℤ) ≤ H := by simpa only [Int.natCast_natAbs] using h
  have hx' : x.natAbs ≤ H := by exact_mod_cast hx
  exact ⟨by simpa using hx', by simpa using hH⟩

/-- The input heights charged by the rational dot-product machine are powers of two
whose exponent is linear in the prescribed precision and logarithmic cutoff. -/
theorem computedProxy_input_heights {n : ℕ} (fuel prec : ℕ) {A : ℤ} (c : ℤ)
    (a : Fin n → ℤ) (mag : Fin n → ℚ) (hm : ∀ i, 0 < mag i)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^prec * A ≤ 2^fuel) :
    let H := (2 : ℕ)^(prec+2+fuel)
    let data i := (logProxyNumerator fuel prec (mag i)).getD 0
    (∀ i, ((smallProxyLeft (2^(prec+2)) a) i).num.natAbs ≤ H ∧
      ((smallProxyLeft (2^(prec+2)) a) i).den ≤ H) ∧
    (∀ i, ((smallProxyRight c data) i).num.natAbs ≤ H ∧ ((smallProxyRight c data) i).den ≤ H) := by
  let H : ℕ := 2^(prec+2+fuel)
  let D : ℕ := 2^(prec+2)
  let T : ℤ := 2^fuel
  let grid i := (logProxyNumerator fuel prec (mag i)).getD 0
  have hH : 1 ≤ H := one_le_pow₀ (by decide : (1 : ℕ) ≤ 2)
  have hprod : (H : ℤ) = (D : ℤ) * T := by simp [H,D,T,pow_add]
  have hD' : 1 ≤ D := one_le_pow₀ (by decide : (1 : ℕ) ≤ 2)
  have hD : (1 : ℤ) ≤ D := by exact_mod_cast hD'
  have hT : (1 : ℤ) ≤ T := one_le_pow₀ (by decide : (1 : ℤ) ≤ 2)
  have hAH : 0 ≤ A := le_trans (add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) hform
  have hAT : A ≤ T := (le_mul_of_one_le_left hAH (one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2))).trans hcut
  have hTH : T ≤ H := hprod ▸ le_mul_of_one_le_left (by omega) hD
  have hDH : (D : ℤ) ≤ H := hprod ▸ le_mul_of_one_le_right (by omega) hT
  have hc : |c| ≤ (H : ℤ) := (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans
    (hform.trans (hAT.trans hTH))
  have ha (i : Fin n) : |a i| ≤ (H : ℤ) := by
    have hsum : |a i| ≤ ∑ j, |a j| := Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    exact hsum.trans ((le_add_of_nonneg_left (abs_nonneg _)).trans (hform.trans (hAT.trans hTH)))
  have hg (i : Fin n) : |grid i| ≤ (H : ℤ) := by
    cases h : logProxyNumerator fuel prec (mag i) with
    | none =>
      simp [grid,h]
    | some z =>
      have hz := (logProxyNumerator_abs_lt fuel prec (hm i) h).le
      simpa [grid,h,H,pow_add] using hz
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => proxyInt_height hH (ha j)) i
    have h := proxyInt_height hH (show |(D : ℤ)| ≤ (H:ℤ) by simpa using hDH)
    simpa [smallProxyLeft,D] using h
  · intro i
    exact Fin.cases (proxyInt_height hH hc) (fun j => proxyInt_height hH (hg j)) i

end Compression
end LinearProgramming
end Optimization
end OAI
