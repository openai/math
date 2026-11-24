import OAI.Computability.VPVNP.MarkedTensor
import OAI.Computability.VPVNP.ExteriorLevelRates

/-!
# Tensor powers of a marked index

In the proof of Lemma A.1, the same tensor power is placed at three different
parties. Regrouping the marked indices of its copies gives a single index of
dimension `q ^ n`, with the same coefficient table at each placement. The
rounded exterior levels then bound both terms of the split by the same geometric
mean to the power `n`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

universe u v
variable {k : Type u} {J : Type v}

/-- The product of `n` copies of the coefficient table, with their marked indices
grouped separately from the background coordinates. -/
def markedPowerTable [CommMonoid k] {B : J → Type} {I : Type} (n : ℕ)
    (T : ((j : J) → B j) → I → k) (b : (j : J) → Fin n → B j) (i : Fin n → I) : k :=
  ∏ t, T (fun j ↦ b j t) (i t)


/-- Moving a marked index preserves whether the coefficient array is zero. -/
theorem marked_coeff_eq_zero_iff [Zero k] (B : J → Type) [∀ j, Fintype (B j)]
    (I : Type) [Fintype I] (a : J) (T : ((j : J) → B j) → I → k) :
    (marked B I a T).coeff = 0 ↔ T = 0 := by
  constructor
  · intro h
    funext b i
    exact congrFun h (fun j ↦ (b j, fun _ ↦ i))
  · rintro rfl
    rfl

variable [Field k] [Fintype J]

/-- The regrouped marked array and the product of the original tensors have
mutually invertible local changes of basis, including for the zeroth power. -/
theorem marked_power_mutual (B : J → Type) [∀ j, Fintype (B j)] (I : Type) [Fintype I]
    (a : J) (T : ((j : J) → B j) → I → k) (n : ℕ) :
    let P := marked (fun j ↦ Fin n → B j) (Fin n → I) a (markedPowerTable n T)
    let U := tensorFamilyProduct (fun _ : Fin n ↦ marked B I a T)
    Restricts P U ∧ Restricts U P := by
  let e (j : J) : (Fin n → B j × (j = a → I)) ≃ (Fin n → B j) × (j = a → Fin n → I) :=
    { toFun := fun x ↦ (fun t ↦ (x t).1, fun h t ↦ (x t).2 h)
      invFun := fun x t ↦ (x.1 t, fun h ↦ x.2 h t)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact restricts_of_reindex e (fun _ ↦ rfl)

/-- Spectral values of the regrouped marked table are the powers of the values
at the original placement. -/
theorem SpectralPoint.value_markedPower (F : SpectralPoint k J) (B : J → Type)
    [∀ j, Fintype (B j)] (I : Type) [Fintype I] (a : J) (T : ((j : J) → B j) → I → k)
    (n : ℕ) :
    F.value (marked (fun j ↦ Fin n → B j) (Fin n → I) a (markedPowerTable n T)) =
      F.value (marked B I a T) ^ n := by
  rw [F.value_eq_of_mutual (marked_power_mutual B I a T n), F.value_tensorFamilyProduct]
  simp

/-- Relabeling the marked index preserves the tensor up to invertible local
changes of basis. The background coordinates are arbitrary. -/
theorem marked_reindex_mutual (B : J → Type) [∀ j, Fintype (B j)] {I K : Type}
    [Fintype I] [Fintype K] (e : I ≃ K) (a : J) (T : ((j : J) → B j) → I → k) :
    Restricts (marked B I a T) (marked B K a (fun b i ↦ T b (e.symm i))) ∧
      Restricts (marked B K a (fun b i ↦ T b (e.symm i))) (marked B I a T) := by
  let f (j : J) : (B j × (j = a → K)) ≃ (B j × (j = a → I)) :=
    { toFun := fun x ↦ (x.1, fun h ↦ e.symm (x.2 h))
      invFun := fun x ↦ (x.1, fun h ↦ e (x.2 h))
      left_inv := fun x ↦ by simp
      right_inv := fun x ↦ by simp }
  exact restricts_of_reindex f (fun _ ↦ rfl)

/-- The index set used for the exterior operators on the powered tensor. -/
noncomputable def markedPowerIndex (I : Type) [Fintype I] (n : ℕ) :
    (Fin n → I) ≃ Fin (Fintype.card I ^ n) :=
  Fintype.equivFinOfCardEq (by simp)

/-- The coefficient table with the marked tuples numbered from zero to `q ^ n - 1`
has the original spectral value to the `n`th power at every placement. -/
theorem SpectralPoint.value_markedPower_fin (F : SpectralPoint k J) (B : J → Type)
    [∀ j, Fintype (B j)] (I : Type) [Fintype I] (a : J) (T : ((j : J) → B j) → I → k)
    (n : ℕ) :
    F.value (marked (fun j ↦ Fin n → B j) (Fin (Fintype.card I ^ n)) a
      (fun b i ↦ markedPowerTable n T b ((markedPowerIndex I n).symm i))) =
        F.value (marked B I a T) ^ n := by
  rw [← F.value_eq_of_mutual (marked_reindex_mutual _ (markedPowerIndex I n) a (markedPowerTable n T))]
  exact F.value_markedPower B I a T n

open VPVNP.ExteriorLevelRates

/-- Moving the index in both directions puts the balancing exponent in the
interval of exponents attainable by exterior powers. -/
theorem relocation_log_bounds {q : ℕ} {y z t : ℝ} (hq : 2 ≤ q)
    (hy : 0 < y) (hz : 0 < z) (ht : 0 < t)
    (hzy : z ≤ (q : ℝ) ^ t * y) (hyz : y ≤ (q : ℝ) ^ t * z) :
    -1 ≤ Real.logb q (z / y) / t ∧ Real.logb q (z / y) / t ≤ 1 := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast (show 1 < q from hq)
  have upper := (Real.logb_le_iff_le_rpow hq' (div_pos hz hy)).2 ((div_le_iff₀ hy).2 hzy)
  have lower := (Real.logb_le_iff_le_rpow hq' (div_pos hy hz)).2 ((div_le_iff₀ hz).2 hyz)
  rw [Real.logb_div hz.ne' hy.ne'] at upper ⊢
  rw [Real.logb_div hy.ne' hz.ne'] at lower
  exact ⟨(le_div_iff₀ ht).2 (by linarith), (div_le_iff₀ ht).2 (by linarith)⟩

/-- Compare a contribution from one endpoint to the target using its
logarithmic dimension bound. -/
private theorem exterior_term_le {q a d w e m : ℝ} {n : ℕ}
    (hq : 1 < q) (ha : 0 < a) (hd : 0 < d) (hw : 0 < w) (he : 0 ≤ e)
    (hlog : Real.logb q d ≤ m * n)
    (hbal : Real.logb q a + e * m = Real.logb q w) :
    a ^ n * d ^ e ≤ w ^ n := by
  by_contra! h
  have hstrict := (Real.logb_lt_logb_iff hq (pow_pos hw n)
    (mul_pos (pow_pos ha n) (Real.rpow_pos_of_pos hd _))).2 h
  rw [Real.logb_mul (pow_ne_zero _ ha.ne') (Real.rpow_pos_of_pos hd _).ne',
    Real.logb_pow, Real.logb_pow, Real.logb_rpow_eq_mul_logb_of_pos hd, ← hbal] at hstrict
  nlinarith only [hstrict, mul_le_mul_of_nonneg_left hlog he]

/-- The positive powers and the two adjacent binomial ratios imply the
geometric interpolation inequality for the marked tensor. -/
theorem relocation_of_power_bounds {q : ℕ} {x y z u t : ℝ} (hq : 2 ≤ q)
    (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1)
    (hs₀ : -1 ≤ Real.logb q (z / y) / t) (hs₁ : Real.logb q (z / y) / t ≤ 1)
    (hpow : ∀ n : ℕ, 1 ≤ n → ∀ b : ℕ, 1 ≤ b → b < q ^ n →
      x ^ n ≤ y ^ n * (((q ^ n).choose (b + 1) : ℝ) / (q ^ n).choose b) ^ ((1 - u) * t) +
        z ^ n * (((q ^ n).choose (b - 1) : ℝ) / (q ^ n).choose b) ^ (u * t)) :
    x ≤ z ^ (1 - u) * y ^ u := by
  let w := z ^ (1 - u) * y ^ u
  let s := Real.logb q (z / y) / t
  have hw : 0 < w := mul_pos (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hy _)
  have hq' : (1 : ℝ) < q := by exact_mod_cast (show 1 < q from hq)
  have hst : t * s = Real.logb q z - Real.logb q y := by
    dsimp [s]
    rw [Real.logb_div hz.ne' hy.ne']
    field_simp
  have hwlog : Real.logb q w = (1 - u) * Real.logb q z + u * Real.logb q y := by
    dsimp [w]
    rw [Real.logb_mul (Real.rpow_pos_of_pos hz _).ne' (Real.rpow_pos_of_pos hy _).ne',
      Real.logb_rpow_eq_mul_logb_of_pos hz, Real.logb_rpow_eq_mul_logb_of_pos hy]
  by_contra! hx
  obtain ⟨n, hn', hn⟩ := ((Filter.eventually_ge_atTop (1 : ℕ)).and
    ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hw).2 hx)).eventually_gt_atTop 2)).exists
  change 2 < (x / w) ^ n at hn
  let b := powerLevel q s n
  obtain ⟨hb, hbQ, ⟨_, hup⟩, ⟨_, hdown⟩⟩ := powerLevel_log_bounds hq hn' hs₀ hs₁
  obtain ⟨hbpos, huppos, hdownpos⟩ := choose_adjacent_pos hb hbQ
  have hden : (0 : ℝ) < (q ^ n).choose b := by exact_mod_cast hbpos
  have hup_pos : (0 : ℝ) < (q ^ n).choose (b + 1) := by exact_mod_cast huppos
  have hdown_pos : (0 : ℝ) < (q ^ n).choose (b - 1) := by exact_mod_cast hdownpos
  have hup_term := exterior_term_le hq' hy (div_pos hup_pos hden) hw
    (mul_nonneg (sub_nonneg.mpr hu₁) ht.le) hup (by rw [hwlog]; nlinarith [congrArg (· * u) hst])
  have hdown_term := exterior_term_le hq' hz (div_pos hdown_pos hden) hw
    (mul_nonneg hu₀ ht.le) hdown (by rw [hwlog]; nlinarith [congrArg (· * u) hst])
  rw [div_pow, lt_div_iff₀ (pow_pos hw n)] at hn
  linarith only [hn, hpow n hn' b hb hbQ, hup_term, hdown_term]

end WireTensor

end VPVNP
end Computability
end OAI
