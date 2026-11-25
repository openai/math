import OAI.Computability.NearSquareRoot.SynchronizedTensor
import OAI.Computability.NearSquareRoot.SynchronizedNorm
import OAI.Computability.NearSquareRoot.Precision
import OAI.Computability.NearSquareRoot.PrecisionCarryConvolution
import OAI.Computability.NearSquareRoot.PrecisionDigitBounds

/-! # Recovery on the padded product of cyclic axes

Instantiate the fixed-point error analysis with the exact padded residue-box transform.
On valid addresses, nearest-integer recovery then returns the integer cyclic convolution.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ResidueFourier

open SynchronizedPadding Matrix WithLp
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ) [∀ i, NeZero (a i)]

abbrev PaddedBox := (i : ι) → ZMod (a i) ⊕ Fin (b i)

/-- The transform of the manuscript on its full padded address set as a Euclidean isometry. -/
def paddedIsometry : EuclideanSpace ℂ (PaddedBox a b) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (PaddedBox a b) :=
  matrixIsometry _ (tensorMatrix_axisPadding_unitary (B := fun i => Fin (b i))
    (fun i => axisMatrix (a i)) (fun i => axisMatrix_unitary (a i)))

/-- Padded operand array in the Euclidean norm. -/
def paddedArray (f : Box a → ℂ) : EuclideanSpace ℂ (PaddedBox a b) :=
  toLp 2 (zeroExtend (fun i => Fin (b i)) f)

theorem paddedIsometry_spectral_product (f g : Box a → ℂ) :
    let U := paddedIsometry a b
    Real.sqrt (Fintype.card (Box a)) •
      U.symm (pointwiseProduct (U (paddedArray a b f)) (U (paddedArray a b g))) =
      paddedArray a b (convolution f g) := by
  dsimp only
  simp only [paddedIsometry, paddedArray, matrixIsometry_apply, pointwiseProduct,
    matrixIsometry_symm_apply]
  ext i
  have h := congrFun (padded_recover (a := a) b f g) i
  exact h

/-- After both CRT permutations, padded spectral multiplication gives the ordinary coefficient
of a nonaliased pair of digit lists at its original rank. -/
theorem paddedIsometry_ordinary {S h : ℕ} [NeZero S] (e : ZMod S ≃+ Box a)
    (f g : Fin S → ℕ) (hf : ∀ i, h ≤ i.val → f i = 0) (hg : ∀ i, h ≤ i.val → g i = 0)
    (hS : 2*h ≤ S) (t : Fin S) :
    let U := paddedIsometry a b
    let x := paddedArray a b (cyclicDigit f ∘ e.symm)
    let y := paddedArray a b (cyclicDigit g ∘ e.symm)
    let i := occupied (fun j => Fin (b j)) (e (ZMod.finEquiv S t))
    ((Real.sqrt (Fintype.card (Box a)) • U.symm (pointwiseProduct (U x) (U y))) i) =
      (ordinaryCoefficient f g t : ℂ) := by
  dsimp only
  rw [paddedIsometry_spectral_product]
  change zeroExtend _ _ (occupied _ _) = _
  rw [zeroExtend_occupied, convolution_reindex, e.symm_apply_apply]
  exact cyclicDigit_convolution f g hf hg hS t

theorem scale_le_capacity {k : ℕ} (hcard : Fintype.card (PaddedBox a b) ≤ 2^k) :
    |Real.sqrt (Fintype.card (Box a))| ≤ (2 : ℝ)^k := by
  have h := Fintype.card_le_of_injective _ (occupied_injective (A := fun i => ZMod (a i))
    (fun j => Fin (b j)))
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt _ ≤ (Fintype.card (Box a) : ℝ) := Real.sqrt_le_self_iff.mpr
      (Or.inr (by exact_mod_cast Fintype.card_pos (α := Box a)))
    _ ≤ _ := by exact_mod_cast h.trans hcard

/-- The input norm bound follows from the maximum input digit and the size
of the physical (padded) array. -/
theorem paddedDigit_norm {S : ℕ} [NeZero S] {n : ℕ} (hn : 2 ≤ n)
    (e : ZMod S ≃+ Box a) (f : Fin S → ℕ) (hf : ∀ i, f i < 2^DigitPacking.width n)
    (hcard : Fintype.card (PaddedBox a b) = DigitPacking.capacity n) :
    ‖paddedArray a b (cyclicDigit f ∘ e.symm)‖ ≤ (2 : ℝ)^(4*DigitPacking.addressBits n) := by
  apply DigitPacking.digit_array_norm hn hcard
  intro x
  by_cases hx : x ∈ Set.range (occupied (A := fun i => ZMod (a i)) (fun i => Fin (b i)))
  · obtain ⟨y, rfl⟩ := hx
    simp [paddedArray, cyclicDigit, zeroExtend_occupied]
    exact_mod_cast (hf _).le
  · simp [paddedArray, zeroExtend_off _ _ hx]

/-- Given the transform and component rounding accuracies of the manuscript, the output
on every occupied address is precisely the integer residue-box convolution coefficient. -/
theorem recover_integer_on_padded_box (f g : Box a → ℤ)
    {q s' : ℝ} (hq : 2 ≤ q) (hdim : (Fintype.card (PaddedBox a b) : ℝ) ≤ q)
    {x' y' p w out : EuclideanSpace ℂ (PaddedBox a b)}
    (hadjoint : ‖p‖ ≤ q ^ (12 : ℤ) → ‖w - (paddedIsometry a b).symm p‖ ≤ q ^ (-40 : ℤ))
    (ha : ‖paddedArray a b (fun x => (f x : ℂ))‖ ≤ q ^ (4 : ℤ))
    (hb : ‖paddedArray a b (fun x => (g x : ℂ))‖ ≤ q ^ (4 : ℤ))
    (hex : ‖x' - paddedIsometry a b (paddedArray a b (fun x => (f x : ℂ)))‖ ≤ q ^ (-40 : ℤ))
    (hey : ‖y' - paddedIsometry a b (paddedArray a b (fun x => (g x : ℂ)))‖ ≤ q ^ (-40 : ℤ))
    (hp : ∀ i, ‖p i - x' i * y' i‖ ≤ q ^ (-70 : ℤ))
    (hs : |Real.sqrt (Fintype.card (Box a))| ≤ q)
    (hes : |s' - Real.sqrt (Fintype.card (Box a))| ≤ q ^ (-70 : ℤ))
    (hout : ∀ i, ‖out i - s' • w i‖ ≤ q ^ (-70 : ℤ)) :
    ∀ x : Box a, round (out (occupied (fun i => Fin (b i)) x)).re = ∑ y, f y * g (x - y) := by
  have h := (roundedConvolutionRecovers hq hdim (paddedIsometry a b) hadjoint
    ha hb hex hey hp hs hes hout).2
  intro x
  apply h
  rw [paddedIsometry_spectral_product]
  change (zeroExtend (R := ℂ) (fun i => Fin (b i)) _ (occupied (fun i => Fin (b i)) x)).re = _
  rw [zeroExtend_occupied]
  simp [convolution, Complex.mul_re]

end
end ResidueFourier

end NearSquareRoot
end Computability
end OAI
