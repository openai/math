import OAI.LinearAlgebra.FiniteFourier.Feedback.FeedbackTransfer
import OAI.LinearAlgebra.FiniteFourier.Feedback.WalkCount
import OAI.LinearAlgebra.FiniteFourier.BatchedDictionary
import Mathlib.LinearAlgebra.Vandermonde

/-! # Delay dilation in a Vandermonde basis

Evaluate the polynomial transfer numerator at distinct scalar delays. In the
monomial basis on the time slots, truncate the walks just before degree d.
All tails factor through the same s states. Clearing the denominator before
evaluation keeps the family polynomial when the delays coalesce at one.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Polynomial
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {I O : Type} {s : ℕ} (F : Feedback K I O s)

def delayNumerator (z : K) : Matrix O I K :=
  (F.transferDenom.eval 1)⁻¹ • F.transferNumer.map (evalRingHom z)

theorem delayNumerator_one (h : F.Regular) : delayNumerator F 1 = F.matrix := by
  have hn : F.transferDenom.eval 1 ≠ 0 := by rwa [F.eval_one_transferDenom]
  rw [← F.eval_one_rationalTransfer h]
  ext o i
  simp [delayNumerator, F.eval_rationalTransfer_entry hn, div_eq_mul_inv, mul_comm]

private def delayWeight (z : K) := (F.transferDenom.eval 1)⁻¹ * F.transferDenom.eval z

private def delayState (z : K) :=
  (F.transferDenom.eval 1)⁻¹ • (F.readState * (1 - z • F.stateMatrix).adjugate)

private theorem delay_map_eval {m n : Type*} (M : Matrix m n K) (z : K) :
    M.map ((evalRingHom z).comp C) = M := by
  ext; simp

private theorem delay_direct (z : K) :
    delayNumerator F z = delayWeight F z • F.readInput +
      z • (delayState F z * F.inputMatrix) := by
  unfold delayNumerator delayWeight delayState
  rw [F.map_transferNumer, F.map_statePencil]
  simp only [delay_map_eval, coe_evalRingHom, eval_X, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, smul_smul, mul_comm z (F.transferDenom.eval 1)⁻¹]

private theorem delay_recurrence (z : K) :
    delayState F z = delayWeight F z • F.readState + z • (delayState F z * F.stateMatrix) := by
  have eq : delayState F z * (1 - z • F.stateMatrix) = delayWeight F z • F.readState := by
    unfold delayState delayWeight
    rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, F.eval_transferDenom z]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul] at eq
  exact sub_eq_iff_eq_add.mp eq

private def walkCoeff (k : ℕ) : Matrix O I K :=
  fun o i => PowerSeries.coeff k (F.delaySeries o i)

private theorem delay_truncate (z : K) (h : ℕ) :
    delayNumerator F z =
      delayWeight F z • (∑ k ∈ Finset.range (h+1), z^k • walkCoeff F k) +
      z^(h+1) • (delayState F z * (F.stateMatrix ^ h * F.inputMatrix)) := by
  induction h with
  | zero =>
    have hz : walkCoeff F 0 = F.readInput := Matrix.ext F.coeff_zero_delaySeries
    simpa [hz] using delay_direct F z
  | succ h ih =>
    have hs : walkCoeff F (h+1) = F.readState * F.stateMatrix ^ h * F.inputMatrix :=
      Matrix.ext (F.coeff_succ_delaySeries h)
    rw [ih, Finset.sum_range_succ _ (h+1), hs, smul_add, add_assoc]
    congr 1
    conv_lhs => rw [delay_recurrence F z]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, smul_add, smul_comm (z^(h+1)) (delayWeight F z),
      ← Matrix.mul_assoc F.readState, smul_smul (z^(h+1)) z, ← pow_succ, Matrix.mul_assoc (delayState F z),
      ← Matrix.mul_assoc F.stateMatrix, ← pow_succ']

variable {d : ℕ} (t : Fin d → K)

private def delayLeft (o : O) : Matrix (Fin d) (Fin s) K :=
  fun a k => (t a)^d * delayState F (t a) o k

private def delayRight (d : ℕ) (i : I) : Matrix (Fin s) (Fin d) K :=
  fun k j => (F.stateMatrix ^ (d - 1 - j.val) * F.inputMatrix) k i

private def delayShort (o : O) (i : I) : Matrix (Fin d) (Fin d) K :=
  fun a j => (delayWeight F (t a) •
    (∑ k ∈ Finset.range (d - 1 - j.val + 1), (t a)^k • walkCoeff F k)) o i * (t a)^j.val

private theorem delay_basis (o : O) (i : I) :
    Matrix.diagonal (fun a => delayNumerator F (t a) o i) * vandermonde t =
      delayLeft F t o * delayRight F d i + delayShort F t o i := by
  ext a j
  rw [Matrix.diagonal_mul, vandermonde_apply, delay_truncate F _ (d - 1 - j.val),
    Matrix.add_apply, add_mul, add_comm, Matrix.add_apply]
  congr 1
  rw [Matrix.smul_apply, smul_eq_mul, mul_right_comm, ← pow_add,
    show d - 1 - j.val + 1 + j.val = d by omega]
  simp only [delayLeft, delayRight, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

private theorem delay_interpolate (ht : Function.Injective t) (o : O) (i : I) :
    Matrix.diagonal (fun a => delayNumerator F (t a) o i) =
      delayLeft F t o * (delayRight F d i * (vandermonde t)⁻¹) +
      delayShort F t o i * (vandermonde t)⁻¹ := by
  have hv := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ht)
  rw [← Matrix.mul_assoc, ← Matrix.add_mul, ← delay_basis, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hv, Matrix.mul_one]

variable [Fintype I]

private def walkInputs (d : ℕ) (o : O) : Finset I :=
  (Finset.range d).biUnion fun k =>
    (F.outputSupport k (fun _ : Fin 1 => o)).image (fun x => x 0)

private theorem walkInputs_card (d : ℕ) (o : O) :
    (walkInputs F d o).card ≤ d * 2^d := by
  unfold walkInputs
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _k ∈ Finset.range d, 2^d := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.card_image_le.trans ((F.card_outputSupport k 1 _).trans
        (Nat.pow_le_pow_right (by decide) (Finset.mem_range.mp hk).le))
    _ = _ := by simp

private theorem delayShort_zero (o : O) (i : I) (hi : i ∉ walkInputs F d o) :
    delayShort F t o i = 0 := by
  ext a j
  have hz (k : ℕ) (hk : k ∈ Finset.range (d - 1 - j.val + 1)) : walkCoeff F k o i = 0 := by
    by_contra hn
    apply hi
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hk
      omega), Finset.mem_image.mpr ⟨fun _ => i, ?_, rfl⟩⟩
    simpa [Feedback.outputSupport, Fin.prod_univ_one, walkCoeff] using hn
  simp only [delayShort, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.zero_apply]
  rw [Finset.sum_eq_zero (fun k hk => by rw [hz k hk, mul_zero]), mul_zero, zero_mul]

/-- The tails for all d slots share a factor of width s. A short walk can
reach at most d times 2^d inputs, each with d time coordinates. -/
theorem delay_rank_support [Fintype O] (ht : Function.Injective t) :
    ∃ B Z : Matrix (O × Fin d) (I × Fin d) K,
      B.rank ≤ s ∧ matrixEntryCount Z ≤ (Fintype.card O * d) * (d * 2^d * d) ∧
      Matrix.blockDiagonal (fun a => delayNumerator F (t a)) = B + Z := by
  let L : Matrix (O × Fin d) (Fin s) K := fun oa => delayLeft F t oa.1 oa.2
  let R : Matrix (Fin s) (I × Fin d) K := fun k ib =>
    (delayRight F d ib.1 * (vandermonde t)⁻¹) k ib.2
  let Z : Matrix (O × Fin d) (I × Fin d) K := fun oa ib =>
    (delayShort F t oa.1 ib.1 * (vandermonde t)⁻¹) oa.2 ib.2
  refine ⟨L * R, Z, (rank_mul_le_left _ _).trans (by simpa using rank_le_card_width L), ?_, ?_⟩
  · rw [matrixEntryCount_eq_sum]
    calc
      _ ≤ ∑ _oa : O × Fin d, d * 2^d * d := by
        apply Finset.sum_le_sum
        rintro ⟨o,a⟩ _
        apply le_trans (b := ((walkInputs F d o) ×ˢ (Finset.univ : Finset (Fin d))).card)
        · apply Finset.card_le_card
          rintro ⟨i,b⟩ hi
          simp only [Finset.mem_product, Finset.mem_univ, and_true]
          by_contra h
          exact (Finset.mem_filter.mp hi).2 (by simp [Z, delayShort_zero F t o i h])
        · rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
          exact Nat.mul_le_mul_right d (walkInputs_card F d o)
      _ = _ := by simp
  · ext ⟨o,a⟩ ⟨i,b⟩
    have h := congrFun (congrFun (delay_interpolate F t ht o i) a) b
    simpa only [Matrix.blockDiagonal_apply', Matrix.diagonal_apply, Matrix.add_apply,
      Matrix.mul_apply] using! h

end
end FiniteFourier
end LinearAlgebra
end OAI
