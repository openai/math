import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Separation
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Powers
import OAI.LinearAlgebra.TensorSpectrum.TagWords

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# Coefficient tensor words and matched-label restrictions

Tensor powers of a shared-first-leg tensor have one branch for each word.
The regrouping below preserves all coefficients, including the zero
coefficients between different words. Selecting words by an injection is an
actual local restriction. Multiplicativity is then applied to the actual
tensor product represented by each word.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagTensorWords

variable {X Y Z : Type*}

/-- A shared-first-leg tensor with an arbitrary finite label type. -/
def sharedLabels {ι : Type*} [DecidableEq ι] (A : ι → Tensor O X Y Z) :
    Tensor O X (ι × Y) (ι × Z) :=
  fun x y z => if y.1 = z.1 then A y.1 x y.2 z.2 else 0

/-- One actual tensor factor per position, without identifying positions or
discarding any coefficients. -/
def tensorWord {N : ℕ} (B : Fin N → Tensor O X Y Z) :
    Tensor O (Fin N → X) (Fin N → Y) (Fin N → Z) :=
  fun x y z => ∏ j, B j (x j) (y j) (z j)

/-- A word specifies which branch occupies each tensor position. -/
def wordBranch {s N : ℕ} (A : Fin s → Tensor O X Y Z)
    (w : TagWords.Word s N) :
    Tensor O (Fin N → X) (Fin N → Y) (Fin N → Z) :=
  tensorWord (fun j => A (w j))

/-- Put a word of labels and a word of coordinates back into coordinate pairs. -/
def joinCoordinates (N : ℕ) (ι U : Type*) :
    ((Fin N → ι) × (Fin N → U)) ≃ (Fin N → ι × U) where
  toFun p j := (p.1 j, p.2 j)
  invFun f := (fun j => (f j).1, fun j => (f j).2)
  left_inv p := by
    rcases p with ⟨a, b⟩
    rfl
  right_inv f := by
    funext j
    exact Prod.eta (f j)

/-- Regrouping the second and third coordinates of the full tensor power
produces exactly the shared tensor of word branches. -/
theorem power_shared_pullback {s N : ℕ} (A : Fin s → Tensor O X Y Z) :
    Tensor.pullback (Equiv.refl (Fin N → X))
      (joinCoordinates N (Fin s) Y) (joinCoordinates N (Fin s) Z)
      (Tensor.power (Separation.shared A) N) = sharedLabels (wordBranch A) := by
  classical
  funext x y z
  by_cases h : y.1 = z.1
  · simp only [Tensor.pullback, Equiv.refl_apply, Tensor.power,
      sharedLabels, ite_eq_left h, wordBranch, tensorWord]
    apply Finset.prod_congr rfl
    intro j hj
    simp [Separation.shared, joinCoordinates, congrFun h j]
  · have hex : ∃ j, y.1 j ≠ z.1 j := by
      by_contra hnone
      apply h
      funext j
      by_contra hj
      exact hnone ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hex
    simp only [Tensor.pullback, Equiv.refl_apply, Tensor.power,
      sharedLabels, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Separation.shared, joinCoordinates, hj]

section Restriction

variable [Fintype X] [Fintype Y] [Fintype Z]

/-- The regrouping is implemented by three actual coordinate pullbacks. -/
theorem restricts_power_shared_words {s N : ℕ}
    (A : Fin s → Tensor O X Y Z) :
    CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N)
      (sharedLabels (wordBranch (N := N) A)) := by
  rw [← power_shared_pullback]
  exact CoefficientTensor.Restricts.pullback _ _ _ _

/-- The regrouping is invertible, so it also identifies the tensor classes. -/
theorem ofTensor_shared_words {s N : ℕ} (A : Fin s → Tensor O X Y Z) :
    TensorClass.ofTensor (sharedLabels (wordBranch (N := N) A)) =
      TensorClass.ofTensor (Separation.shared A) ^ N := by
  rw [← power_shared_pullback, TensorClass.ofTensor_pullback_equiv,
    TensorClass.ofTensor_power]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- An injection on branch labels preserves the equality test between labels. -/
theorem shared_injective_pullback {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (A : ι → Tensor O X Y Z) (e : κ → ι) (he : Function.Injective e) :
    Tensor.pullback id (fun y : κ × Y => (e y.1, y.2))
      (fun z : κ × Z => (e z.1, z.2)) (sharedLabels A) =
      sharedLabels (fun i => A (e i)) := by
  funext x y z
  by_cases h : y.1 = z.1
  · simp [Tensor.pullback, sharedLabels, h]
  · have h' : e y.1 ≠ e z.1 := fun h' => h (he h')
    simp [Tensor.pullback, sharedLabels, h, h']

/-- Selecting any set of matched labels is an actual local restriction. -/
theorem restricts_shared_injective {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (A : ι → Tensor O X Y Z) (e : κ → ι) (he : Function.Injective e) :
    CoefficientTensor.Restricts (sharedLabels A) (sharedLabels (fun i => A (e i))) := by
  rw [← shared_injective_pullback A e he]
  exact CoefficientTensor.Restricts.pullback _ _ _ _

/-- This target uses the precise `Fin M` shared tensor accepted by the charged
separation construction. The label map may enumerate any selected word set. -/
theorem restricts_power_shared_selected {s N M : ℕ}
    (A : Fin s → Tensor O X Y Z) (e : Fin M → TagWords.Word s N)
    (he : Function.Injective e) :
    CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N)
      (Separation.shared (fun i => wordBranch A (e i))) := by
  have h := (restricts_power_shared_words A).trans
    (restricts_shared_injective (wordBranch A) e he)
  have heq : sharedLabels (fun i => wordBranch A (e i)) =
      Separation.shared (fun i => wordBranch A (e i)) := by
    funext x y z
    by_cases hlabel : y.1 = z.1 <;>
      simp [sharedLabels, Separation.shared, hlabel]
  rw [← heq]
  exact h

/-- In particular, the words in a count fiber can be retained together. -/
theorem restricts_power_shared_fiber {s N : ℕ}
    (A : Fin s → Tensor O X Y Z) (c : TagWords.CountVector s N) :
    CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N)
      (sharedLabels (fun w : {w // w ∈ TagWords.fiber c} => wordBranch A w.val)) := by
  exact (restricts_power_shared_words A).trans
    (restricts_shared_injective (wordBranch A) Subtype.val Subtype.val_injective)

/-- Every finite enumeration of a count fiber provides the exact input needed
by charged separation, with multiplicity equal to the number of selected words. -/
theorem restricts_power_shared_fiber_enumeration {s N M : ℕ}
    (A : Fin s → Tensor O X Y Z) (c : TagWords.CountVector s N)
    (e : Fin M ≃ {w // w ∈ TagWords.fiber c}) :
    CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N)
      (Separation.shared (fun i => wordBranch A (e i).val)) := by
  exact restricts_power_shared_selected A (fun i => (e i).val)
    (Subtype.val_injective.comp e.injective)

end Restriction

/-- Split off the first tensor position, leaving every remaining coordinate. -/
def headTailCoordinates (N : ℕ) (U : Type*) :
    (Fin (N + 1) → U) ≃ U × (Fin N → U) where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  right_inv p := by
    rcases p with ⟨u, f⟩
    rfl

section Character

variable [Fintype X] [Fintype Y] [Fintype Z]

/-- The class of a coefficient tensor word is the product of the factor
classes. This is proved by actual invertible coordinate regroupings. -/
theorem ofTensor_tensorWord {N : ℕ} (B : Fin N → Tensor O X Y Z) :
    TensorClass.ofTensor (tensorWord B) = ∏ j, TensorClass.ofTensor (B j) := by
  induction N with
  | zero =>
    rw [show (∏ j : Fin 0, TensorClass.ofTensor (B j)) = 1 by simp]
    change TensorClass.ofTensor (tensorWord B) =
      TensorClass.ofTensor TensorClass.unitTensor
    have heq : Tensor.pullback (Equiv.ofUnique (Fin 0 → X) PUnit)
        (Equiv.ofUnique (Fin 0 → Y) PUnit) (Equiv.ofUnique (Fin 0 → Z) PUnit)
        TensorClass.unitTensor = tensorWord B := by
      funext x y z
      simp [Tensor.pullback, tensorWord, TensorClass.unitTensor]
    rw [← heq]
    exact TensorClass.ofTensor_pullback_equiv _ _ _ _
  | succ N ih =>
    rw [Fin.prod_univ_succ, ← ih (fun j => B j.succ), TensorClass.ofTensor_mul]
    have heq : Tensor.pullback (headTailCoordinates N X)
        (headTailCoordinates N Y) (headTailCoordinates N Z)
        (Tensor.product (B 0) (tensorWord (fun j => B j.succ))) = tensorWord B := by
      funext x y z
      simp [Tensor.pullback, Tensor.product, tensorWord, headTailCoordinates,
        Fin.prod_univ_succ]
    rw [← heq]
    exact TensorClass.ofTensor_pullback_equiv _ _ _ _

/-- A character evaluates a word branch as the finite product of the values
of the chosen branches; there is no separate multiplicativity assumption. -/
theorem map_wordBranch (f : TensorClass.Character) {s N : ℕ}
    (A : Fin s → Tensor O X Y Z) (w : TagWords.Word s N) :
    f (TensorClass.ofTensor (wordBranch A w)) =
      TagWords.wordWeight (fun i => f (TensorClass.ofTensor (A i))) w := by
  unfold wordBranch TagWords.wordWeight
  rw [ofTensor_tensorWord]
  exact map_prod f.toHom _ _

/-- Every word in a fixed count fiber has the same character value. -/
theorem map_wordBranch_of_mem_fiber (f : TensorClass.Character) {s N : ℕ}
    (A : Fin s → Tensor O X Y Z) {c : TagWords.CountVector s N}
    {w : TagWords.Word s N} (hw : w ∈ TagWords.fiber c) :
    f (TensorClass.ofTensor (wordBranch A w)) =
      TagWords.countWeight (fun i => f (TensorClass.ofTensor (A i))) c := by
  rw [map_wordBranch]
  exact TagWords.wordWeight_eq_of_mem_fiber _ hw

end Character

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagTensorWords
