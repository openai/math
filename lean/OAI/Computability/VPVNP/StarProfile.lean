import OAI.Computability.VPVNP.ContractionValue
import OAI.Computability.VPVNP.StarPacking
import OAI.Computability.VPVNP.StarGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The width profile of a spectral point

Theorem 2.4 takes the supremum of the normalized spectral values of nonzero
tensors with local dimensions `2 ^ (h * w j)`. The coordinate rank bound
makes this supremum finite. It controls arbitrary covectors on a powered star,
including entangled covectors and the power zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u

namespace WireTensor

variable {J : Type} {k : Type u}

/-- A positive height and a nonzero tensor of the dimensions of the width profile. -/
structure StarWitness (k : Type u) [Zero k] (w : J → ℕ) where
  /-- Positive integer scaling the logarithmic local dimensions in a witness for the width
  profile. -/
  height : ℕ
  positive : 0 < height
  /-- Nonzero tensor coefficient array with local dimension `2 ^ (height * w j)` at party `j`. -/
  coeff : Array k (fun j ↦ Fin (2 ^ (height * w j)))
  nonzero : coeff ≠ 0

namespace StarWitness

variable [Field k] {w : J → ℕ}

/-- Package the coefficients and the prescribed bases into an old-party tensor. -/
def tensor (W : StarWitness k w) : Tensor k J :=
  .mk _ (fun _ ↦ inferInstance) W.coeff

instance : Nonempty (StarWitness k w) := by
  refine ⟨⟨1, by decide, fun _ ↦ 1, ?_⟩⟩
  intro h
  exact one_ne_zero (congrFun h (fun j ↦ ⟨0, Nat.pow_pos (by decide)⟩))

end StarWitness

namespace SpectralPoint

variable [Field k] [Fintype J] [Nonempty J] (F : SpectralPoint k J)

/-- The supremum in equation (2.1), for a fixed integer width at every old party. -/
noncomputable def starRate (w : J → ℕ) : ℝ :=
  sSup (Set.range (fun W : StarWitness k w ↦ Real.logb 2 (F.value W.tensor) / W.height))

theorem starWitness_pos {w : J → ℕ} (W : StarWitness k w) : 0 < (F.value W.tensor : ℝ) := by
  exact_mod_cast zero_lt_one.trans_le (F.one_le_value W.tensor W.nonzero)

/-- Coordinate rank bounds each normalized logarithm by the sum of local widths. -/
theorem starWitness_log_le {w : J → ℕ} (W : StarWitness k w) :
    Real.logb 2 (F.value W.tensor) / W.height ≤ (∑ j, w j : ℕ) := by
  have hcard (j : J) : Fintype.card (W.tensor.Basis j) = 2 ^ (W.height * w j) :=
    (Fintype.card_congr (show W.tensor.Basis j ≃ Fin (2 ^ (W.height * w j)) from
      Equiv.refl _)).trans (Fintype.card_fin _)
  have hdim : (∏ j, Fintype.card (W.tensor.Basis j)) = 2 ^ (W.height * ∑ j, w j) := by
    simp only [hcard, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
  have hval := F.value_le_basis_product W.tensor
  rw [hdim] at hval
  have hval' : (F.value W.tensor : ℝ) ≤ (2 : ℝ) ^ (W.height * ∑ j, w j) := by exact_mod_cast hval
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (F.starWitness_pos W) hval'
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  apply (div_le_iff₀ (show 0 < (W.height : ℝ) by exact_mod_cast W.positive)).mpr
  simpa only [Nat.cast_mul, mul_comm] using hlog

/-- The defining supremum is the least upper bound of a nonempty, bounded set. -/
theorem starRate_isLUB (w : J → ℕ) :
    IsLUB (Set.range (fun W : StarWitness k w ↦ Real.logb 2 (F.value W.tensor) / W.height))
      (F.starRate w) := by
  refine isLUB_csSup (Set.range_nonempty _) ?_
  refine ⟨((∑ j, w j : ℕ) : ℝ), ?_⟩
  rintro _ ⟨W, rfl⟩
  exact F.starWitness_log_le W

theorem starRate_le_sum (w : J → ℕ) : F.starRate w ≤ (∑ j, w j : ℕ) :=
  (F.starRate_isLUB w).2 (fun _ ⟨W, hW⟩ ↦ hW ▸ F.starWitness_log_le W)

theorem starRate_nonneg (w : J → ℕ) : 0 ≤ F.starRate w := by
  let W := Classical.choice (inferInstance : Nonempty (StarWitness k w))
  have h1 : 1 ≤ (F.value W.tensor : ℝ) := by exact_mod_cast F.one_le_value W.tensor W.nonzero
  exact (div_nonneg (Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) h1) (Nat.cast_nonneg _)).trans
    ((F.starRate_isLUB w).1 (Set.mem_range_self W))

/-- Apply the profile to arbitrary finite local bases of the prescribed cardinalities. -/
theorem value_le_starRate {w : J → ℕ} (n : ℕ) (T : Tensor k J)
    (hdim : ∀ j, Fintype.card (T.Basis j) = 2 ^ (n * w j)) :
    (F.value T : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * F.starRate w) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hval := F.value_le_basis_product T
    simpa [hdim] using (NNReal.coe_le_coe.mpr hval)
  by_cases hz : T.coeff = 0
  · rw [F.value_zero _ hz]
    exact Real.rpow_nonneg (by norm_num) _
  let e (j : J) := Fintype.equivFinOfCardEq (hdim j)
  let W : StarWitness k w :=
    { height := n, positive := Nat.pos_of_ne_zero hn,
      coeff := fun x ↦ T.coeff (fun j ↦ (e j).symm (x j))
      nonzero := by
        intro h
        apply hz
        funext x
        simpa only [Equiv.symm_apply_apply, Pi.zero_apply] using congrFun h (fun j ↦ e j (x j)) }
  have heq : F.value T = F.value W.tensor :=
    F.value_eq_of_mutual (restricts_of_reindex (fun j ↦ (e j).symm) (fun _ ↦ rfl))
  rw [heq]
  apply (Real.logb_le_iff_le_rpow (by norm_num : 1 < (2 : ℝ)) (F.starWitness_pos W)).mp
  have h := (F.starRate_isLUB w).1 (Set.mem_range_self W)
  change Real.logb 2 (F.value W.tensor) / (n : ℝ) ≤ F.starRate w at h
  rw [mul_comm]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mp h

/-- An arbitrary contraction of a star power has the advertised spectral upper bound. -/
theorem starPower_contraction_le (w : J → ℕ) (n : ℕ)
    (ξ : (tensorPowerFin n (starTensor (k := k) (fun j ↦ Fin (2 ^ w j)))).Basis none → k) :
    (F.value (contractCenter (tensorPowerFin n (starTensor (fun j ↦ Fin (2 ^ w j)))) ξ) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * F.starRate w) := by
  apply F.value_le_starRate
  intro j
  change Fintype.card (Fin n → Fin (2 ^ w j)) = _
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

omit [Nonempty J] in
/-- Finite powers have the usual spectral value, also at exponent zero. -/
theorem value_tensorPowerFin (n : ℕ) (T : Tensor k J) :
    F.value (tensorPowerFin n T) = F.value T ^ n := by
  have h := F.value_tensorFamilyProduct (fun _ : Fin n ↦ T)
  calc
    F.value (tensorPowerFin n T) = F.value (tensorFamilyProduct (fun _ : Fin n ↦ T)) :=
      F.value_eq_of_mutual (restricts_of_reindex (fun _ ↦ Equiv.refl _) (fun _ ↦ rfl))
    _ = _ := by simpa using h

omit [Nonempty J] in
/-- The packed copies and their simple padding have exactly the value of the unpadded power. -/
theorem starPower_exists_packed (w : J → ℕ) (W : StarWitness k w) (n : ℕ) :
    ∃ ξ, (F.value W.tensor : ℝ) ^ (n / W.height) =
      F.value (contractCenter (tensorPowerFin n (starTensor (fun j ↦ Fin (2 ^ w j)))) ξ) := by
  obtain ⟨ξ, hξ⟩ := exists_starPowerFin_packing W.tensor w W.height n
    (fun j ↦ Fintype.card_fin _)
  refine ⟨ξ, ?_⟩
  exact_mod_cast (F.value_tensorPowerFin _ _).symm.trans (F.value_eq_of_mutual hξ)

/-- Real upper bound on the supremum over all center covectors. -/
theorem contractionValue_starPower_le (w : J → ℕ) (n : ℕ) :
    (F.contractionValue (tensorPowerFin n (starTensor (fun j ↦ Fin (2 ^ w j)))) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * F.starRate w) := by
  apply (F.isLUB_contractionValue _).2
  rintro _ ⟨ξ, rfl⟩
  exact F.starPower_contraction_le w n ξ

/-- The contraction values of the powered old factor and star in the proof
of Theorem 2.4 have the prescribed exponential rate. -/
theorem starPower_contractionRoot (T : Tensor k J) (w : J → ℕ) (u : ℕ) :
    Filter.Tendsto (fun m : ℕ ↦
      (F.contractionValue (tensorProduct (embedOld (tensorPowerFin m T))
        (tensorPowerFin (u * m) (starTensor (fun j ↦ Fin (2 ^ w j))))) : ℝ) ^ (m : ℝ)⁻¹)
      Filter.atTop (nhds ((F.value T : ℝ) * (2 : ℝ) ^ ((u : ℝ) * F.starRate w))) := by
  apply VPVNP.Spectral.starContractionRoot_tendsto (StarWitness.height (w := w) (k := k))
    (fun W ↦ (F.value W.tensor : ℝ)) u _ (by positivity) (fun W ↦ F.starWitness_pos W)
    (F.starRate_isLUB w)
  · intro W m _
    obtain ⟨ξ, hξ⟩ := F.starPower_exists_packed w W (u * m)
    rw [F.contractionValue_old_product, F.value_tensorPowerFin, NNReal.coe_mul, NNReal.coe_pow, hξ]
    exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (F.value_le_contractionValue _ ξ))
      (by positivity)
  · intro m _
    rw [F.contractionValue_old_product, F.value_tensorPowerFin, NNReal.coe_mul, NNReal.coe_pow, mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (F.contractionValue_starPower_le w (u * m)).trans_eq ?_
    rw [← Real.rpow_mul_natCast (by norm_num), Nat.cast_mul]
    ring_nf

omit [Nonempty J] in
/-- The spectral value of the dyadic star is the exponential of its weighted wire sum. -/
theorem value_dyadicStar (H : SpectralPoint k (Option J)) (w : J → ℕ) :
    (H.value (starTensor (fun j ↦ Fin (2 ^ w j))) : ℝ) =
      (2 : ℝ) ^ (∑ j, (w j : ℝ) * H.wireDistance none (some j)) := by
  rw [← H.value_eq_of_mutual (starTensor_wireNetwork (fun j ↦ Fin (2 ^ w j)))]
  exact H.value_binary_wireNetwork _ _ w

/-- Every extension of the given spectral point has weighted star length at
least the old width-profile rate. -/
theorem starRate_le_extension (H : SpectralPoint k (Option J))
    (extendsOld : ∀ T, H.value (embedOld T) = F.value T) (w : J → ℕ) :
    F.starRate w ≤ ∑ j, (w j : ℝ) * H.wireDistance none (some j) := by
  apply (F.starRate_isLUB w).2
  rintro _ ⟨W, rfl⟩
  let w' (j : J) := W.height * w j
  have hrest := restricts_embedOld_contractCenter (starTensor (fun j ↦ Fin (2 ^ w' j))) W.coeff
  rw [contractCenter_starTensor] at hrest
  have hval : (F.value W.tensor : ℝ) ≤ (H.value (starTensor (fun j ↦ Fin (2 ^ w' j))) : ℝ) := by
    rw [← extendsOld]
    exact_mod_cast H.monotone hrest
  rw [value_dyadicStar H w'] at hval
  have hlog := (Real.logb_le_iff_le_rpow (by norm_num : 1 < (2 : ℝ)) (F.starWitness_pos W)).mpr hval
  apply (div_le_iff₀ (show 0 < (W.height : ℝ) by exact_mod_cast W.positive)).mpr
  rw [mul_comm, Finset.mul_sum]
  simpa only [w', Nat.cast_mul, mul_assoc] using hlog

end SpectralPoint
end WireTensor

end VPVNP
end Computability
end OAI
