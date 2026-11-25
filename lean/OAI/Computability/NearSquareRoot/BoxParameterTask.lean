import OAI.Computability.NearSquareRoot.BoxScale
import OAI.Computability.IntegerMultiplication.Carry.Figure

/-! # Computing the axis search parameters from a unary address width

The P192 header programs compute the binary magnitudes using charged addition,
products, division and exponentiation. Conversion to a tally calls `Figure.pay`,
whose premise bounds the numerical value by a polynomial in the input size.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxParameterTask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry
open IntegerMultiplication.Staff IntegerMultiplication.Strip BoxScale

private def input : Regime Tally := ⟨size, send, Dom.base _⟩

private theorem address : Realizes input (fun t : Tally => t.length) := by
  change Poly (fun t : Tally => tally t.length)
  simpa only [recover_tally] using (Poly.identity (X := Tally))

private theorem length_dom : Dom input.scale (fun t : Tally => t.length) :=
  (Dom.base _).mono fun t => (duration t).le

private theorem span_dom : Dom input.scale (fun t : Tally => span t.length) := by
  refine (((Dom.const input.scale 2).mul (length_dom.add (Dom.const _ 1))).pow 20).mono ?_
  intro t
  by_cases h : 1 < t.length
  · exact (span_le h).trans (Nat.pow_le_pow_left (by omega) _)
  · have hsmall : t.length = 0 ∨ t.length = 1 := by omega
    rcases hsmall with e | e <;> rw [e] <;> decide

theorem width_poly : Poly (fun t : Tally => tally (width t.length)) :=
  Realizes.times (Realizes.fix (r := input) 20) (Figure.of_spoken address).short_log

private theorem span_figure : Figure input (fun t : Tally => span t.length) :=
  Figure.repeated (Figure.natural 2)
    (show Realizes input (fun t : Tally => width t.length) from width_poly)

theorem span_poly : Poly (fun t : Tally => tally (span t.length)) :=
  span_figure.pay span_dom

theorem window_poly : Poly (fun t : Tally => tally (span t.length / t.length ^ 2)) := by
  have sq := (Figure.of_spoken address).multiplied (Figure.of_spoken address)
  rw [show (fun t : Tally => tally (span t.length / t.length ^ 2)) =
      (fun t : Tally => tally (span t.length / (t.length * t.length))) by simp [pow_two]]
  exact (span_figure.quotients sq).pay (span_dom.mono fun _ => Nat.div_le_self ..)

theorem count_poly : Poly (fun t : Tally => tally (count t.length)) :=
  Realizes.dividing address (show Realizes input (fun t : Tally => width t.length) from width_poly)

theorem remainder_poly : Poly (fun t : Tally => tally (t.length % width t.length)) :=
  Realizes.rem address (show Realizes input (fun t : Tally => width t.length) from width_poly)

theorem remainderSpan_poly : Poly (fun t : Tally => tally (2 ^ (t.length % width t.length))) := by
  have hf := Figure.repeated (Figure.natural 2)
    (show Realizes input (fun t : Tally => t.length % width t.length) from remainder_poly)
  apply hf.pay
  refine ((Dom.const input.scale 2).mul span_dom).mono ?_
  intro t
  by_cases h : 1 < t.length
  · have hr := (remainder_lt h).le
    exact (Nat.pow_le_pow_right (by decide) hr).trans (Nat.le_mul_of_pos_left _ (by decide))
  · have hsmall : t.length = 0 ∨ t.length = 1 := by omega
    rcases hsmall with e | e <;> rw [e] <;> decide

/-- The five unary fields of the search header, in order: padded axis span,
search window length, full-axis count, full-axis width, and final-axis width. -/
def parameters (t : Tally) : Tally × Tally × Tally × Tally × Tally :=
  (tally (span t.length), tally (span t.length / t.length ^ 2), tally (count t.length),
    tally (width t.length), tally (t.length % width t.length))

theorem parameters_poly : Poly parameters :=
  span_poly.pair (window_poly.pair (count_poly.pair (width_poly.pair remainder_poly)))

end BoxParameterTask

end NearSquareRoot
end Computability
end OAI
