import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.ChargedSeparation
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.DotsPower
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagTensorWords

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# The exact finite-word character inequality

Every count fiber is selected by actual local coordinate maps from a tensor
power of the original shared-input tensor.  Charged separation is then applied
to that finite fiber.  This is the tensor input to the later scalar limit;
neither the separation nor the word restriction is an assumption here.
-/

noncomputable section

open scoped BigOperators NNReal
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

theorem Character.shared_branch_le (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ} (A : Fin s → Tensor O X Y Z) (i : Fin s) :
    f (ofTensor (A i)) ≤ f (ofTensor (Separation.shared A)) := by
  have hr := CoefficientTensor.Restricts.pullback (Separation.shared A)
    id (fun y => (i, y)) (fun z => (i, z))
  have heq : Tensor.pullback id (fun y => (i, y)) (fun z => (i, z))
      (Separation.shared A) = A i := by
    funext x y z
    simp [Tensor.pullback, Separation.shared]
  rw [heq] at hr
  exact f.monotone' (ofTensor_le hr)

theorem Character.one_le_of_tensor_unit (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor O X Y Z) (hT : ∃ x y z, T x y z = 1) : 1 ≤ f (ofTensor T) := by
  have h := f.monotone' (ofTensor_le
    (CoefficientTensor.unit_restricts_natTensor_one hT))
  have hunit : ofTensor (CoefficientTensor.natTensor 1) = (1 : TensorClass) := by
    simpa only [Nat.cast_one] using (natCast_eq_ofTensor_natTensor 1).symm
  calc
    1 = f.toHom (ofTensor (CoefficientTensor.natTensor 1)) := by
      rw [hunit]
      exact f.toHom.map_one.symm
    _ ≤ f.toHom (ofTensor T) := h

/-- The original word-fiber cost, including the fixed factor six.  The
polynomial number of possible count vectors has not yet been removed. -/
theorem Character.tag_count_fiber (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s N : ℕ} (A : Fin s → Tensor O X Y Z)
    (c : TagWords.CountVector s N) (hc : 0 < (TagWords.fiber c).card) :
    ((TagWords.fiber c).card : ℝ) ^ f.pX *
        TagWords.countWeight (fun i => (f (ofTensor (A i)) : ℝ)) c ≤
      6 * (f (ofTensor (Separation.shared A)) : ℝ) ^ N := by
  classical
  let M := (TagWords.fiber c).card
  let e : Fin M ≃ {w // w ∈ TagWords.fiber c} :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe (TagWords.fiber c))).symm
  let B := fun i : Fin M => TagTensorWords.wordBranch A (e i).val
  let C : ℝ≥0 := TagWords.countWeight (fun i => f (ofTensor (A i))) c
  have hvalue : ∀ i, f (ofTensor (B i)) = C := by
    intro i
    exact TagTensorWords.map_wordBranch_of_mem_fiber f A (e i).property
  have hsep := f.charged_separation_equal hc B C hvalue
  have hselect := TagTensorWords.restricts_power_shared_fiber_enumeration A c e
  have hmono : f (ofTensor (Separation.shared B)) ≤
      (f (ofTensor (Separation.shared A))) ^ N := by
    have h := f.monotone' (ofTensor_le hselect)
    simpa only [Character.map_power_tensor] using h
  have hfinite : C * f (dotX M) ≤
      6 * (f (ofTensor (Separation.shared A))) ^ N :=
    hsep.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
  have hreal : (C : ℝ) * f.dotXValue M ≤
      6 * (f (ofTensor (Separation.shared A)) : ℝ) ^ N := by
    exact_mod_cast hfinite
  rw [f.dotXValue_eq_rpow M (Nat.succ_le_iff.mpr hc)] at hreal
  have hC : (C : ℝ) =
      TagWords.countWeight (fun i => (f (ofTensor (A i)) : ℝ)) c := by
    simp [C, TagWords.countWeight]
  rw [hC, mul_comm] at hreal
  exact hreal

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass
