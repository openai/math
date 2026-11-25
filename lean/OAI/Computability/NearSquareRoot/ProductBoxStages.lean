import OAI.Computability.NearSquareRoot.ProductReindex
import OAI.Computability.NearSquareRoot.SynchronizedBoxWord
import OAI.Computability.NearSquareRoot.SynchronizedStageUnitary
import OAI.Computability.NearSquareRoot.SynchronizedRecovery

/-! # Rounded programs for the synchronized words on a valid coprime box -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductRecovery

open Matrix Kronecker ShortFourier SynchronizedPadding SynchronizedBlocks FixedPoint ProductMatrixLayers
noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A S : ι → Type}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Exchange the designated bit and spectator fields for the finite-record butterfly. -/
def bitFirst {X T : Type} (e : X ≃ Fin 2 × T) : X ≃ T × Bool :=
  e.trans ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv))

omit [Fintype ι] [∀ i, Fintype (A i)] [∀ i, Fintype (S i)] in
theorem selected_block (act : Finset ι) (bits : ∀ i, A i ≃ Fin 2 × S i)
    (i : ι) (hi : i ∈ act) :
    SynchronizedSelected.block act bits i =
      (butterflyMatrix (S i)).submatrix (bitFirst (bits i)) (bitFirst (bits i)) := by
  ext x y
  simp [SynchronizedSelected.block, hi, butterflyMatrix, bitFirst,
    Matrix.one_apply, Matrix.kroneckerMap_apply, ite_mul]

variable {X : Type} [Fintype X] [DecidableEq X] {k : ℕ}

/-- A single stage can be evaluated on finite records with the stated local accuracy. -/
def RoundedStage (k : ℕ) (M : Square X) (hu : Mᴴ * M = 1) : Prop :=
  ∃ step : (X → Record k) → (X → Record k), ∀ r, ‖recordArray r‖ ≤ (2:ℝ)^(13*k) →
    ‖recordArray (step r) - matrixIsometry M hu (recordArray r)‖ ≤ 1/(2:ℝ)^(50*k)

omit [Fintype X] in
private theorem atTick_mem (w : List (Square X)) {j : ℕ} (hj : j < w.length) :
    atTick w j ∈ w := by
  have hr : j < w.reverse.length := by simpa
  simp [atTick, List.getElem?_eq_getElem hr]

/-- A word of certified local record passes supplies the rounded transform in
physical application order. Only local properties of members of the word are required. -/
theorem realizable_word (w : List (Square X)) (u : UnitaryFactors w)
    (bound : w.length ≤ 2^(10*k))
    (ops : ∀ M, (hm : M ∈ w) → RoundedStage k M (u M hm))
    (U : Square X) (hU : Uᴴ * U = 1) (factor : w.prod = U) :
    ∃ F : Layers X k, F.count = w.length ∧
      F.Approximates (matrixIsometry U hU).toLinearIsometry := by
  classical
  let step (j : ℕ) := if hj : j < w.length then (ops _ (atTick_mem w hj)).choose else id
  refine ⟨Layers.fromMatrices w u step, rfl, ?_⟩
  apply Layers.fromMatrices_approximates w u step bound _ U hU factor
  intro j hj r hr
  dsimp only [step]
  split
  · exact (ops _ (atTick_mem w hj)).choose_spec r hr
  · contradiction

theorem box_depth_bound {k L : ℕ} (hk : 1024 ≤ k) (hL : L ≤ k) :
    7560000*(L+2) ≤ 2^(10*k) := by
  have hl : L+2 ≤ 2^(k+1) := by
    have h := Nat.lt_two_pow_self (n := k+1)
    omega
  calc
    _ ≤ 2^23 * 2^(k+1) := Nat.mul_le_mul (by decide) hl
    _ = 2^(23+(k+1)) := (Nat.pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- A valid box supplies exact Fourier factorizations and their layer counts.
To realize both directions it suffices to implement each of its three allowed
stage shapes to the local record accuracy. -/
theorem valid_box_programs {k L : ℕ} {box : List (ℕ × ℕ)} (h : BoxShape.Valid k L box)
    [∀ i, NeZero (BoxFin.modulus box i)] (hd : 4 ≤ box.length) (hk : 1024 ≤ k) (hL : L ≤ k)
    (realize : ∀ M (hs : BoxStage hd (boxBits h) M), RoundedStage k M hs.unitary) :
    let a := BoxFin.modulus box
    let b := BoxFin.padding box
    let U := ResidueFourier.paddedIsometry a b
    ∃ F J : Layers (ResidueFourier.PaddedBox a b) k,
      F.count = 7560000*(L+2) ∧ J.count = 7560000*(L+2) ∧
      F.Approximates U.toLinearIsometry ∧ J.Approximates U.symm.toLinearIsometry := by
  dsimp only
  let M := paddedFourier box
  have hM : Mᴴ * M = 1 := tensorMatrix_axisPadding_unitary
    (B := fun i => Fin (BoxFin.padding box i)) _ (fun i => ResidueFourier.axisMatrix_unitary _)
  have run {w : List (Square (∀ i, BoxAxis box i))} (hw : ∀ A ∈ w, BoxStage hd (boxBits h) A)
      (hl : w.length = 7560000*(L+2)) (target : Square (∀ i, BoxAxis box i))
      (u : targetᴴ * target = 1) (eq : w.prod = target) :=
    realizable_word w (fun A ha => (hw A ha).unitary) (by rw [hl]; exact box_depth_bound hk hL)
      (fun A ha => realize A (hw A ha)) target u eq
  obtain ⟨w, he, hw, hl⟩ := valid_box_word_with_layout h hd (boxBits h) false
  obtain ⟨F, hlenF, hF⟩ := run hw hl M hM he
  obtain ⟨v, he', hv, hl'⟩ := valid_box_word_with_layout h hd (boxBits h) true
  have hM' : Mᴴᴴ * Mᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr hM)
  obtain ⟨J, hlenJ, hJ⟩ := run hv hl' Mᴴ hM' he'
  refine ⟨F, J, hlenF.trans hl, hlenJ.trans hl', hF, ?_⟩
  convert hJ using 1
  ext x i
  exact congrFun (congrArg WithLp.ofLp (matrixIsometry_symm_apply M hM (WithLp.ofLp x))) i

end
end ProductRecovery

end NearSquareRoot
end Computability
end OAI
