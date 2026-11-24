import OAI.Computability.VPVNP.SliceArithmeticPowerPorts
import OAI.Computability.VPVNP.SliceArithmeticConstant
import OAI.Computability.VPVNP.SliceArithmeticZero

/-!
# Initializing inversion on packed field-element stacks

The controller copies the exponent advice to a consumable stack, scans the
input for zero and installs the appropriate packed constant in the multiplier's
accumulator. Starting at zero for zero input handles the field of order two,
whose Fermat exponent is zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.InverseCall

open RAMTape TapeWord
open SliceArithmeticRound (packed)

private def zeroPorts : SliceArithmeticZero.Port → Port
  | .input => .inr .base
  | .flag => .inr .flag
  | .scratch => .inr .scratch

private def literalPorts : ScanPort → Port
  | .left => .inl (.inr .coeff)
  | .right => .inr .temp
  | .tmp => .inr .scratch
  | .out => .inl (.inr .acc)

private def copyExponent : FiniteRoutine Port :=
  SuccessorFields.prependCopy (.inr .exponent) (.inr .bits) (.inr .scratch)

private def testZero : FiniteRoutine Port := SliceArithmeticZero.machine.onPorts zeroPorts

private def putLiteral (b : Bool) : FiniteRoutine Port :=
  (SliceArithmeticConstant.machine b).onPorts literalPorts

private def chooseLiteral : FiniteRoutine Port :=
  .ofRoutine (Routine.popCase (.inr .flag) (Routine.halt false) (putLiteral true).body (putLiteral false).body)

/-- Fixed stack instructions for installing the exponent scan and initial accumulator. -/
def initializeInput : FiniteRoutine Port := (copyExponent.followedBy testZero).followedBy chooseLiteral

private theorem copyExponent_runs (p e w : ℕ) (cb base exponent : List Bool) :
    copyExponent.Runs (5 * exponent.length + 2) (frame p e w cb base exponent [] [] [])
      (frame p e w cb base exponent exponent [] []) := by
  let s := frame p e w cb base exponent [] [] []
  have hr := SuccessorFields.prependCopy_runs (.inr Extra.exponent : Port) (.inr Extra.bits)
    (.inr Extra.scratch) (by decide) (by decide) (by decide) s rfl
  have hu : Function.update s (.inr .bits) (s (.inr .exponent) ++ s (.inr .bits)) =
      frame p e w cb base exponent exponent [] [] := by
    funext i
    rcases i with i|i
    · rfl
    · cases i <;> simp [s, frame, Function.update]
  exact hu ▸ hr

variable {p e w : ℕ} [Fact p.Prime]

private theorem testZero_runs (hw : Word.workingWidth p ≤ w) (c a : Vector p e) (exp : List Bool) :
    let cb := packed w (List.ofFn c)
    let ab := packed w (List.ofFn a)
    testZero.Runs (4 * (e*w) + 3) (frame p e w cb ab exp exp [] [])
      (frame p e w cb ab exp exp [] [decide (a = zero p e)]) := by
  intro cb ab
  apply SliceArithmeticZero.machine.runs_onPorts_framed (ports := zeroPorts)
    (by intro i j h; cases i <;> cases j <;> simp_all [zeroPorts]) (SliceArithmeticZero.vector_runs hw a [])
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · rintro (i|i) hi
    · rfl
    · cases i <;> first | rfl | exact (hi .flag rfl).elim

private theorem putLiteral_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w) (c : Vector p e)
    (base exp : List Bool) (b : Bool) :
    let cb := packed w (List.ofFn c)
    (putLiteral b).Runs (7 * (e*w) + 3) (frame p e w cb base exp exp [] [])
      (frame p e w cb base exp exp (packed w (List.ofFn (SliceArithmeticConstant.literal b p e))) []) := by
  intro cb
  have run := SliceArithmeticConstant.machine_runs he hw b c []
  simp only [List.length_nil, Nat.zero_add] at run
  apply (SliceArithmeticConstant.machine b).runs_onPorts_framed (ports := literalPorts)
    (by intro i j h; cases i <;> cases j <;> simp_all [literalPorts])
    run
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · rintro ((i|i)|i) hi
    · rfl
    · cases i <;> first | rfl | exact (hi .out rfl).elim
    · rfl

private theorem chooseLiteral_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c a : Vector p e) (exp : List Bool) :
    let cb := packed w (List.ofFn c)
    let ab := packed w (List.ofFn a)
    chooseLiteral.Runs (7*(e*w)+3+1) (frame p e w cb ab exp exp [] [decide (a = zero p e)])
      (frame p e w cb ab exp exp (packed w (List.ofFn (if a = zero p e then zero p e else one p e))) []) := by
  intro cb ab
  have hup (flag : Bool) : Function.update (frame p e w cb ab exp exp [] [flag]) (.inr .flag) [] =
      frame p e w cb ab exp exp [] [] := by
    funext i
    rcases i with i|i
    · rfl
    · cases i <;> rfl
  by_cases h : a = zero p e
  · rw [ite_eq_left h, decide_eq_true h]
    apply Routine.runs_popCase_true (.inr Extra.flag : Port) (Routine.halt false) (putLiteral true).body
      (putLiteral false).body (s := frame p e w cb ab exp exp [] [true]) (tail := []) rfl
    rw [hup]
    exact putLiteral_runs he hw c ab exp false
  · rw [ite_eq_right h, decide_eq_false h]
    apply Routine.runs_popCase_false (.inr Extra.flag : Port) (Routine.halt false) (putLiteral true).body
      (putLiteral false).body (s := frame p e w cb ab exp exp [] [false]) (tail := []) rfl
    rw [hup]
    exact putLiteral_runs he hw c ab exp true

/-- The saved exponent and base are preserved, the working bits are installed,
and the flag and temporary stacks are empty upon return. -/
theorem initialize_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c a : Vector p e) (exponent : List Bool) :
    let cb := packed w (List.ofFn c)
    let ab := packed w (List.ofFn a)
    ∃ t ≤ 5 * exponent.length + 11 * (e*w) + 9, initializeInput.Runs t
      (frame p e w cb ab exponent [] [] [])
      (frame p e w cb ab exponent exponent (packed w (List.ofFn (if a = zero p e then zero p e else one p e))) []) := by
  intro cb ab
  exact ⟨_, by omega, ((copyExponent_runs p e w cb ab exponent).followedBy
    (testZero_runs hw c a exponent)).followedBy (chooseLiteral_runs he hw c a exponent)⟩

end SliceArithmetic.InverseCall

end VPVNP
end Computability
end OAI
