import OAI.LinearAlgebra.SpectralBooks.SiteTensor.MovingTensorStep
import OAI.LinearAlgebra.SpectralBooks.MovingIndependent
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Padding

/-! # Joint convexity of arbitrary placed tensors

Pad the local bases to a common dyadic size, which preserves the tensor's
restriction class at every placement. The marks of every tensor power then
have the same dimension in the exterior splitting argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open Filter
open scoped Topology Classical

namespace SiteTensor

open Relocation

variable {J : Type} [Fintype J] [Nonempty J] {K : Type*} [Field K] {r : ℕ}

private def dyadicRoot (T : Raw.{0} (Fin r) K) (hT : T.coeff ≠ 0) (k : ℕ)
    (hcard : ∀ i, Fintype.card (T.Leg i) = 2 ^ k) (n : ℕ) :
    MovingNode J K (fun _ : Fin r => 2 ^ (k*n)) := by
  let R := MovingTensor.ofRaw (J := J) (q := fun _ : Fin r => 2 ^ (k*n)) (T.powerTensor n)
    (fun i => Fintype.equivFinOfCardEq (by
      change Fintype.card (Fin n → T.Leg i) = 2 ^ (k*n)
      simp [hcard, pow_mul]))
  exact (⟨R, T.powerTensor_ne_zero hT n⟩, 0)

private theorem dyadic_admissible
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
    (T : Raw.{0} (Fin r) K) (k : ℕ) (hcard : ∀ i, Fintype.card (T.Leg i) = 2^k)
    (a b : Fin r → J) : CubeTable.AdmissibleGaps (fun i => k * rawWireDistance φ c (a i) (b i))
      (fun x => rawLogPrice φ c (T.group (cornerAt a b x))) := by
  apply CubeTable.admissibleGaps_of_transport
  intro i x
  let p := Function.update (cornerAt a b x) i (a i)
  let v := Function.update (cornerAt a b x) i (b i)
  have h := rawLogPrice_transport φ c hc T p v
  have hsum : (∑ j, rawWireDistance φ c (p j) (v j) * Real.logb 2 (Fintype.card (T.Leg j))) =
      k * rawWireDistance φ c (a i) (b i) := by
    rw [Finset.sum_eq_single i]
    · simp [p, v, hcard, Real.logb_pow, mul_comm]
    · intro j _ hji
      simp [p, v, Function.update_of_ne hji, rawWireDistance_self φ c hc]
    · simp
  rw [hsum] at h
  simpa [CubeTable.gap, cornerAt_update, p, v] using h

private theorem dyadic_coupled [NeZero r]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
    (T : Raw.{0} (Fin r) K) (hT : T.coeff ≠ 0) (k : ℕ) (hk : 0 < k)
    (hcard : ∀ i, Fintype.card (T.Leg i) = 2^k) (a z b : Fin r → J)
    (t : Fin r → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i))
    (π : CubeTable r) (hπ : CubeTable.IsCoupling π t) :
    rawLogPrice φ c (T.group z) ≤ CubeTable.cost π
      (fun e => rawLogPrice φ c (T.group (cornerAt a b e))) := by
  let M : CubeTable r := fun e => rawLogPrice φ c (T.group (cornerAt a b e))
  let endpoint (n : ℕ) (y : MovingNode J K (fun _ : Fin r => 2^(k*n))) (e : Fin r → Bool) :=
    movingNodePrice φ (c/n) y (cornerAt a b e)
  let inside (n : ℕ) (y : MovingNode J K (fun _ : Fin r => 2^(k*n))) := movingNodePrice φ (c/n) y z
  have hw (n : ℕ) (p q : J) : rawWireDistance φ (c/n) p q = rawWireDistance φ c p q / n := by
    unfold rawWireDistance rawLogPrice
    ring
  have rootPrice (n : ℕ) (hn : 0 < n) (p : Fin r → J) :
      movingNodePrice φ (c/n) (dyadicRoot T hT k hcard n) p = rawLogPrice φ c (T.group p) := by
    change rawLogPrice φ (c/n) ((T.powerTensor n).group p) - 0 = _
    rw [sub_zero, rawLogPrice_group_powerTensor]
    unfold rawLogPrice
    field_simp
  apply CubeTable.manySiteCoupledRelocation endpoint inside (dyadicRoot T hT k hcard) M
    (fun i => k * rawWireDistance φ c (a i) (b i)) (dyadic_admissible φ c hc T k hcard a b)
    ht ?_ ?_ ?_ π hπ
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact ⟨(rootPrice n hn z).ge, fun e => (rootPrice n hn _).le⟩
  · intro ε hε N i hmid
    have hsmall := (tendsto_const_div_atTop_nhds_zero_nat c).eventually_lt_const hε
    filter_upwards [eventually_gt_atTop 0, hsmall] with n hn hsc
    refine moving_selectedSplit φ (by positivity) (Nat.mul_pos hk hn) a b z N i ?_ hsc.le
    rw [hw, Nat.cast_mul, mul_assoc, mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0)]
    exact hmid
  · refine .of_forall fun n y => movingNodePrice_independent y φ (c/n) (by positivity) a b z t ht ?_ ?_
    · intro i
      rw [hw, hw, hza, mul_div_assoc]
    · intro i
      rw [hw, hw, hzb, mul_div_assoc]

/-- Proposition 2.5 of the circuit dichotomy paper, at arbitrary finite spectral
points over any field. The coupling has the prescribed marginal at each mark
and the tensor may have arbitrary finite local dimensions. A mark with equal
endpoints is held fixed. -/
theorem rawLogPrice_coupled_relocation
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
    (T : Raw.{0} (Fin r) K) (a z b : Fin r → J) (t : Fin r → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i))
    (π : CubeTable r) (hπ : CubeTable.IsCoupling π t) :
    rawLogPrice φ c (T.group z) ≤ CubeTable.cost π
      (fun e => rawLogPrice φ c (T.group (cornerAt a b e))) := by
  rcases eq_or_ne r 0 with rfl | hr
  · have he (x : Fin 0 → Bool) : cornerAt a b x = z := Subsingleton.elim _ _
    simp only [CubeTable.cost, he, ← Finset.sum_mul, hπ.total, one_mul, le_refl]
  let : NeZero r := ⟨hr⟩
  by_cases hT : T.coeff = 0
  · have hzero (p : Fin r → J) : rawLogPrice φ c (T.group p) = 0 :=
      rawLogPrice_zero φ c _ (funext fun x => congrFun hT _)
    simp [hzero, CubeTable.cost]
  obtain ⟨k,hk,U,hcard,hU⟩ := T.exists_dyadic_padding
  have he (p : Fin r → J) : rawLogPrice φ c (T.group p) = rawLogPrice φ c (U.group p) := by
    change c * Real.logb 2 (φ.val _ : ℝ) = _
    have eqClass : ofRaw (T.group p) = ofRaw (U.group p) := ofRaw_eq_iff.mpr
      ⟨Raw.group_restricts p hU.1, Raw.group_restricts p hU.2⟩
    rw [eqClass]
    rfl
  simp only [he]
  exact dyadic_coupled φ c hc U (hU.coeff_ne_zero_iff.mp hT) k hk hcard a z b t ht hza hzb π hπ

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
