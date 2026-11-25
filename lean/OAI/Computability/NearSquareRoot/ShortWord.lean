import OAI.Computability.IntegerMultiplication.Foundation
import OAI.Computability.NearSquareRoot.ShortWordClock
import OAI.Computability.NearSquareRoot.ShortWordCall
import OAI.Computability.NearSquareRoot.ShortWordFixedPoint

/-!
# Integer products inside an array record

The P192 product is available above its top-level input/output driver. At this
interface a caller can park other records on the stacks. The multiplication
command returns the full product and restores the parked data.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortWord
open IntegerMultiplication

theorem productTask : Code.Task (fun i : Domain => clock (n0 i)) inpSt outSt := by
  obtain ⟨_, b, task, C, hb⟩ := runs_
  apply task.bound C
  intro i
  have hβ : (1 : ℝ) ≤ Param.beta (n0 i) := by
    exact_mod_cast (Nat.le_max_left 1 (Nat.clog 2 (n0 i)))
  have h := Real.rpow_le_self_of_one_le hβ
    (sub_le_self (1 : ℝ) (by positivity : 0 ≤ (2 : ℝ)⁻¹ ^ (182 : ℕ)))
  have hw : budgetB i ≤ (clock (n0 i) : ℝ) := by
    rw [clock, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  have he : (b i : ℝ) + 1 ≤ (C : ℝ) * ((clock (n0 i) : ℝ) + 1) :=
    (hb i).trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg C))
  exact_mod_cast he

/-- The two positive equal-width inputs and the full product can contain leading zeros. -/
theorem productSpec (i : Domain) :
    (Lea.answer (v i)).length = 2 * n0 i ∧
    bitValue (Lea.answer (v i)) = bitValue (v i).1 * bitValue (v i).2 :=
  ⟨Lea.date_length _, Lea.value_answer i.val.property⟩

theorem productOnTapes : PhysicalTask (fun i : Domain => clock (n0 i)) inpSt outSt :=
  physicalTask productTask

namespace FixedPoint

/-- Both magnitudes have positive common word width, with at most that many fractional bits. -/
abbrev Inputs := {i : ProductInput // i.1.1.2.length = i.1.2.2.length ∧
  0 < i.1.1.2.length ∧ i.2.length ≤ i.1.1.2.length}

def magnitudes (x : Inputs) : Domain :=
  ⟨⟨(x.val.1.1.2, x.val.1.2.2), x.property.1⟩, x.property.2.1⟩

def answer (x : Inputs) : SignedWord :=
  truncate (Lea.answer (v (magnitudes x))) (x.val.1.1.1 ^^ x.val.1.2.1) x.val.2.length

/-- One signed fixed-point multiply, including truncation and moving the sign and precision. -/
theorem signedTask : Code.Task (fun x : Inputs => clock x.val.1.1.2.length)
    (fun x => Code.send x.val) (fun x => Code.send (answer x)) := by
  have h := task (fun x : Inputs => x.val) (fun x => Lea.answer (v (magnitudes x)))
    (fun x => clock x.val.1.1.2.length) (productTask.on magnitudes)
  apply h.bound 6
  intro x
  have hl : (Lea.answer (v (magnitudes x))).length = 2 * x.val.1.1.2.length :=
    (productSpec _).1
  have hw : x.val.1.1.2.length ≤ clock x.val.1.1.2.length := by
    apply Nat.le_mul_of_pos_right
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left ..)
  have he := x.property.1
  have hp := x.property.2.2
  omega

theorem signedOnTapes : PhysicalTask (fun x : Inputs => clock x.val.1.1.2.length)
    (fun x => Code.send x.val) (fun x => Code.send (answer x)) :=
  physicalTask signedTask

/-- The trace's signed answer lies within one output grid unit of the real product. -/
theorem signedSpec (x : Inputs) :
    let z := answer x
    let p := x.val.2.length
    z.2.length = 2 * x.val.1.1.2.length - p ∧
      |signedDyadic z.1 (bitValue z.2) p -
        signedDyadic x.val.1.1.1 (bitValue x.val.1.1.2) p *
          signedDyadic x.val.1.2.1 (bitValue x.val.1.2.2) p| < 1 / (2 : ℝ)^p := by
  have ⟨hl, hv⟩ := productSpec (magnitudes x)
  have h := truncate_spec x.val.1.1 x.val.1.2 _ x.val.2.length hv
  exact ⟨h.1.trans (congrArg (fun k => k - x.val.2.length) hl), h.2⟩

end FixedPoint
end ShortWord

end NearSquareRoot
end Computability
end OAI
