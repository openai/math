import OAI.Computability.NearSquareRoot.SynchronizedRecovery
import OAI.Computability.NearSquareRoot.PrecisionDigitBounds
import OAI.Computability.NearSquareRoot.PrecisionRecovery
import OAI.Computability.NearSquareRoot.PrecisionCarry
import OAI.Computability.NearSquareRoot.PrecisionGridQuantization
import OAI.Computability.NearSquareRoot.CRTIsomorphism

/-! # The fixed-point arithmetic and the binary product

Given the actual fixed-width forward and adjoint transform records to the stated
accuracy, all remaining functions in the product stage are fixed-width arithmetic
functions. Their returned most-significant-first word has the correct length and value,
including for inputs with leading zeroes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ResidueFourier

open IntegerMultiplication SynchronizedPadding DigitPacking FixedPoint

noncomputable section
variable {d : ℕ}

/-- Padded, scaled-residue order for an MSF input word. -/
def residueOperand (a b : Fin d → ℕ) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (cop : Pairwise fun i j => (a i).Coprime (a j)) (n : ℕ) (x : Bits.Word) :
    EuclideanSpace ℂ (PaddedBox a b) :=
  paddedArray a b (cyclicDigit (unpackDigits (width n) (∏ i, a i) x) ∘ (CRT.scaled a cop).symm)

/-- Visit the valid inverse-CRT addresses in order, recover each coefficient, retain
its low three radix digits, and run three carry passes. -/
def productWord (a b : Fin d → ℕ) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (cop : Pairwise fun i j => (a i).Coprime (a j)) (n : ℕ)
    (w : PaddedBox a b → Record (addressBits n)) : Bits.Word :=
  let k := addressBits n
  let S := ∏ i, a i
  let e := CRT.scaled a cop
  let s := sqrtRecord (fractionBits k) (componentBits k) S
  let words (t : Fin S) :=
    let i := occupied (fun j => Fin (b j)) (e (ZMod.finEquiv S t))
    Bits.sized (3*width n) (recoverWord (multiply k s (w i)))
  finishCarry (carryPacket n (width n) words)

set_option maxHeartbeats 1400000 in
/-- Every scaled adjoint record at an occupied residue address lies within a
quarter unit of its natural integer convolution coefficient. -/
theorem productRecord_error (a b : Fin d → ℕ) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (cop : Pairwise fun i j => (a i).Coprime (a j)) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card (PaddedBox a b) = capacity n) (hvol : 2*count n ≤ ∏ i, a i)
    (x y : Bits.Word) (hx : x.length = n) (hy : y.length = n)
    (fx fy adj : PaddedBox a b → Record (addressBits n))
    (hfx : ‖recordArray fx - paddedIsometry a b (residueOperand a b cop n x)‖
      ≤ 1/(2:ℝ)^(40*addressBits n))
    (hfy : ‖recordArray fy - paddedIsometry a b (residueOperand a b cop n y)‖
      ≤ 1/(2:ℝ)^(40*addressBits n))
    (hAdj : let p := recordArray (productArray fx fy)
            ‖p‖ ≤ (2:ℝ)^(12*addressBits n) →
              ‖recordArray adj - (paddedIsometry a b).symm p‖ ≤ 1/(2:ℝ)^(40*addressBits n)) (t : Fin (∏ i, a i)) :
    let k := addressBits n
    let S := ∏ i, a i
    let s := sqrtRecord (fractionBits k) (componentBits k) S
    let atRank := occupied (fun j => Fin (b j)) (CRT.scaled a cop (ZMod.finEquiv S t))
    ‖value k (multiply k s (adj atRank)) -
      (ordinaryCoefficient (unpackDigits (width n) S x) (unpackDigits (width n) S y) t : ℂ)‖ ≤ 1/4 := by
  let k := addressBits n
  let S := ∏ i, a i
  let e := CRT.scaled a cop
  have hScard : Fintype.card (Box a) = S := by simp [Box, S, Fintype.card_pi]
  have hcap : Fintype.card (PaddedBox a b) ≤ 2^k := hcard.le
  have hS : S ≤ 2^k := by
    rw [← hScard]
    exact (Fintype.card_le_of_injective _ (occupied_injective (A := fun i => ZMod (a i))
      (fun j => Fin (b j)))).trans hcap
  have hk : 1 ≤ k := by
    have H := width_le_twice_addressBits hn
    have := width_pos hn
    dsimp [k]; omega
  have fits : fractionBits k + k + 1 ≤ componentBits k := by
    unfold fractionBits componentBits; omega
  let s := sqrtRecord (fractionBits k) (componentBits k) S
  let s' : ℝ := (sqrtNumerator S (fractionBits k)) / 2^(fractionBits k)
  have scaleValue : value k s = (s' : ℂ) := sqrtRecord_value _ hS fits
  have scaleErr : |s' - Real.sqrt S| ≤ 1 / (2 : ℝ)^(70*k) := by
    calc
      _ ≤ 1 / (2 : ℝ)^(fractionBits k) := (sqrtNumerator_error S _).le
      _ ≤ _ := by
        apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (by unfold fractionBits; omega)
  have inputNorm (z : Bits.Word) :
      ‖residueOperand a b cop n z‖ ≤ (2 : ℝ)^(4*k) :=
    paddedDigit_norm a b hn e _ (unpackDigits_lt _ _ z) hcard
  have cover := (count_mul_width hn).1
  have nz (z : Bits.Word) (hz : z.length = n) := unpackDigits_eq_zero (m := S) z (show z.length ≤ width n * count n by simpa only [hz] using cover)
    (show count n ≤ S by dsimp [S]; omega)
  let atRank (t : Fin S) := occupied (fun j => Fin (b j)) (e (ZMod.finEquiv S t))
  let target := ordinaryCoefficient (unpackDigits (width n) S x) (unpackDigits (width n) S y)
  have scaleBound := scale_le_capacity a b hcap
  rw [hScard] at scaleBound
  have he := recordConvolution_error hk hcap (paddedIsometry a b) (residueOperand a b cop n x)
    (residueOperand a b cop n y) fx fy adj s (Real.sqrt S) s' scaleValue scaleBound scaleErr
    (inputNorm x) (inputNorm y) hfx hfy hAdj
  have hi := (PiLp.norm_apply_le _ (atRank t)).trans he
  have hc : ((Real.sqrt S) • (paddedIsometry a b).symm (pointwiseProduct
      (paddedIsometry a b (residueOperand a b cop n x))
      (paddedIsometry a b (residueOperand a b cop n y)))) (atRank t) = (target t : ℂ) := by
    rw [← hScard]
    exact paddedIsometry_ordinary a b e _ _ (nz x hx) (nz y hy) hvol t
  rwa [PiLp.sub_apply, hc] at hi

theorem productWord_correct (a b : Fin d → ℕ) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (cop : Pairwise fun i j => (a i).Coprime (a j)) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card (PaddedBox a b) = capacity n) (hvol : 2*count n ≤ ∏ i, a i)
    (x y : Bits.Word) (hx : x.length = n) (hy : y.length = n)
    (fx fy adj : PaddedBox a b → Record (addressBits n))
    (hfx : ‖recordArray fx - paddedIsometry a b (residueOperand a b cop n x)‖
      ≤ 1/(2:ℝ)^(40*addressBits n))
    (hfy : ‖recordArray fy - paddedIsometry a b (residueOperand a b cop n y)‖
      ≤ 1/(2:ℝ)^(40*addressBits n))
    (hAdj : let p := recordArray (productArray fx fy)
            ‖p‖ ≤ (2:ℝ)^(12*addressBits n) →
              ‖recordArray adj - (paddedIsometry a b).symm p‖ ≤ 1/(2:ℝ)^(40*addressBits n)) :
    let z := productWord a b cop n adj
    z.length = 2*n ∧ bitValue z = bitValue x * bitValue y := by
  let k := addressBits n
  let S := ∏ i, a i
  let s := sqrtRecord (fractionBits k) (componentBits k) S
  let atRank (t : Fin S) := occupied (fun j => Fin (b j)) (CRT.scaled a cop (ZMod.finEquiv S t))
  let target := ordinaryCoefficient (unpackDigits (width n) S x) (unpackDigits (width n) S y)
  have cover := (count_mul_width hn).1
  have hfit := count_le_radix hn
  have coeff (t : Fin S) : Bits.value (recoverWord (multiply k s (adj (atRank t)))) = target t :=
    Birch.rests _ _ _ (productRecord_error a b cop hn hcard hvol x y hx hy fx fy adj hfx hfy hAdj t)
  apply finishCarry_product x y hx hy cover hvol
  · intro i
    simp
  · intro i
    rw [Bits.sized_low, coeff, Nat.mod_eq_of_lt]
    exact unpackedCoefficient_lt x y hx hy cover hvol (count_pos hn) hfit i

end
end ResidueFourier

end NearSquareRoot
end Computability
end OAI
