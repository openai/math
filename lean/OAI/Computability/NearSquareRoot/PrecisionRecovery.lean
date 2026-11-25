import OAI.Computability.NearSquareRoot.PrecisionRecordArithmetic
import OAI.Computability.IntegerMultiplication.Birch.Shell

/-! # Recovering exact nonnegative digit coefficients from a rounded transform -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

variable {ι : Type*} [Fintype ι]

/-- Form a nonnegative integer coefficient using P192's finite signed-word
conversion followed by its linear-time add-and-shift operation. -/
def recoverWord {k : ℕ} (x : Record k) : Bits.Word :=
  Birch.roundedG (Code.tally (70 * k), Dusk.mark x)

/-- The word returned by the signed P192 add-half-then-shift procedure is
exactly the integral convolution coefficient. -/
theorem recoverWord_correct {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card ι ≤ 2^k)
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (a b : EuclideanSpace ℂ ι) (x y w : ι → Record k) (scale : Record k)
    (s s' : ℝ) (hscale : value k scale = (s' : ℂ)) (hs : |s| ≤ (2 : ℝ)^k)
    (heScale : |s' - s| ≤ 1 / (2 : ℝ)^(70*k))
    (ha : ‖a‖ ≤ (2 : ℝ)^(4*k)) (hb : ‖b‖ ≤ (2 : ℝ)^(4*k))
    (hx : ‖recordArray x - U a‖ ≤ 1 / (2 : ℝ)^(40*k))
    (hy : ‖recordArray y - U b‖ ≤ 1 / (2 : ℝ)^(40*k))
    (hAdj : let p := recordArray (productArray x y)
            ‖p‖ ≤ (2 : ℝ)^(12*k) → ‖recordArray w - U.symm p‖ ≤ 1 / (2 : ℝ)^(40*k))
    (i : ι) (c : ℕ)
    (hc : ((s • U.symm (pointwiseProduct (U a) (U b))) i) = (c : ℂ)) :
    Bits.value (recoverWord (multiply k scale (w i))) = c := by
  apply Birch.rests (70*k) c
  have he := recordConvolution_error hk hcard U a b x y w scale s s' hscale hs
    heScale ha hb hx hy hAdj
  have hi := (PiLp.norm_apply_le _ i).trans he
  rw [PiLp.sub_apply, hc] at hi
  exact hi

end FixedPoint

end NearSquareRoot
end Computability
end OAI
