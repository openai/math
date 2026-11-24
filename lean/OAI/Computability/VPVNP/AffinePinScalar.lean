import OAI.Computability.VPVNP.SliceArithmeticNeg
import OAI.Computability.VPVNP.SliceArithmeticConstant
import OAI.Computability.VPVNP.RankQueryStackNativeFrames

/-! # Native scalar output for a coordinate pin -/

namespace OAI
namespace Computability
namespace VPVNP

namespace AffinePin.Output

open RAMTape SliceArithmetic RankQuery.Stack

/-- Ports for the active-pin, constant, and unit-monomial bits and the two work stacks used to
write a field literal. -/
inductive Flag where | active | constant | unit | right | tmp
  deriving DecidableEq

instance : Fintype Flag := derive_fintype% _

/-- The field-addition ports and flag ports used to turn a pin value and a monomial
classification into a scalar coefficient. -/
abbrev Port := AddCall.Port ⊕ Flag

/-- Initialize field arithmetic from the modulus and accumulator and install the supplied
active, constant, and unit flag stacks. -/
def frame {p e : ℕ} (c : Vector p e) (v : ℕ) (a z u acc : List Bool) : Stacks Port :=
  Sum.elim (AddCall.clean (MultiplyCall.external p e v (SliceArithmeticRound.packed v (List.ofFn c)) [] acc))
    (fun | .active => a | .constant => z | .unit => u | _ => [])

private def literalPorts : TapeWord.ScanPort → Port
  | .left => .inl (.inr .coeff) | .right => .inr .right | .tmp => .inr .tmp | .out => .inl (.inr .acc)

/-- Negate the pin value for the constant term of an active pin. In the remaining cases write
one for its selected variable and zero otherwise. -/
def operation (active constant unit : Bool) : FiniteRoutine Port :=
  if active && constant then NegCall.machine.onPorts Sum.inl
  else (SliceArithmeticConstant.machine (active && unit)).onPorts literalPorts

/-- Pop one Boolean flag and run the continuation for that bit, rejecting an empty flag stack. -/
def branch (port : Port) (f : Bool → FiniteRoutine Port) : FiniteRoutine Port :=
  .ofRoutine (Routine.popCase port (Routine.halt false) (f false).body (f true).body)

private theorem branch_runs (port : Port) (f : Bool → FiniteRoutine Port)
    {s out : Stacks Port} {b : Bool} {tail : List Bool} {t : ℕ} (hs : s port = b::tail)
    (hr : (f b).Runs t (Function.update s port tail) out) :
    (branch port f).Runs (t+1) s out := by
  cases b
  · exact Routine.runs_popCase_false port _ _ _ hs hr
  · exact Routine.runs_popCase_true port _ _ _ hs hr

/-- Read the active, constant, and unit flags in order and execute the corresponding scalar
operation. -/
def machine : FiniteRoutine Port :=
  branch (.inr .active) fun a => branch (.inr .constant) fun z => branch (.inr .unit) (operation a z)

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

/-- The pin-row coefficient selected by the flags, equal to minus the pin value for the active
constant term, one for the active selected variable, and zero otherwise. -/
def result {c : Vector p e} (a : Scalar c) (active constant unit : Bool) : Scalar c :=
  if active && constant then -a else if active && unit then 1 else 0

/-- Step bound for reading the three classification flags and producing the packed scalar by
negation or literal output. -/
def cost (e v : ℕ) := 8*(e*v) + 5 + AddCall.callCap e v + 3

omit [NeZero e] in
private theorem literal_digits {c : Vector p e} (b : Bool) :
    (if b then (1 : Scalar c) else 0).digits = SliceArithmeticConstant.literal b p e := by
  cases b
  · exact Scalar.digits_pack (zero p e)
  · exact Scalar.digits_pack (one p e)

omit [NeZero e] in
private theorem neg_digits {c : Vector p e} (a : Scalar c) : (-a).digits = fun i => -a.digits i := by
  change (Scalar.pack c (scale (-1) a.digits)).digits = _
  rw [Scalar.digits_pack]
  funext i
  change (-1 : Fin p) * a.digits i = -a.digits i
  exact neg_one_mul _

private theorem operation_runs {c : Vector p e} {v : ℕ} (hv : Word.workingWidth p ≤ v) (a : Scalar c)
    (active constant unit : Bool) : ∃ k ≤ cost e v - 3,
    (operation active constant unit).Runs k (frame c v [] [] [] (Engine.scalar v a))
      (frame c v [] [] [] (Engine.scalar v (result a active constant unit))) := by
  by_cases h : (active && constant) = true
  · simp only [operation, result, h, ite_true]
    obtain ⟨k,hk,run⟩ := NegCall.machine_runs hv a.digits (SliceArithmeticRound.packed v (List.ofFn c))
    refine ⟨k, by unfold cost; omega, ?_⟩
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective run (fun _ => rfl)
    · intro j
      rw [Engine.scalar, neg_digits]
      rfl
    · rintro (j | j) hj
      · exact (hj j rfl).elim
      · rfl
  · simp only [operation, result, ite_eq_right h]
    let b := active && unit
    have run := SliceArithmeticConstant.machine_runs (NeZero.pos e) hv b c (Engine.scalar v a)
    have len : (Engine.scalar v a).length = e*v := by simp [Engine.scalar]
    rw [len] at run
    refine ⟨e*v + 7*(e*v) + 3, by unfold cost; omega, ?_⟩
    apply FiniteRoutine.runs_onPorts_framed _ (ports := literalPorts) (by decide) run
    · intro j; cases j <;> rfl
    · intro j; rw [Engine.scalar, literal_digits (c := c) b]; cases j <;> rfl
    · rintro (j | j) hj
      · rcases j with j | j
        · rfl
        · cases j <;> first | rfl | exact (hj .out rfl).elim
      · cases j <;> rfl

theorem machine_runs {c : Vector p e} {v : ℕ} (hv : Word.workingWidth p ≤ v) (a : Scalar c)
    (active constant unit : Bool) : ∃ k ≤ cost e v,
    machine.Runs k (frame c v [active] [constant] [unit] (Engine.scalar v a))
      (frame c v [] [] [] (Engine.scalar v (result a active constant unit))) := by
  let S := fun A Z U => frame c v A Z U (Engine.scalar v a)
  have ua : Function.update (S [active] [constant] [unit]) (.inr .active) [] = S [] [constant] [unit] := by
    funext i; rcases i with j | j <;> first | cases j <;> rfl
  have uz : Function.update (S [] [constant] [unit]) (.inr .constant) [] = S [] [] [unit] := by
    funext i; rcases i with j | j <;> first | cases j <;> rfl
  have uu : Function.update (S [] [] [unit]) (.inr .unit) [] = S [] [] [] := by
    funext i; rcases i with j | j <;> first | cases j <;> rfl
  obtain ⟨k,hk,hr⟩ := operation_runs hv a active constant unit
  refine ⟨k+3, by unfold cost at *; omega, ?_⟩
  apply branch_runs (.inr .active) _ (b := active) (tail := []) rfl
  rw [ua]
  apply branch_runs (.inr .constant) _ (b := constant) (tail := []) rfl
  rw [uz]
  apply branch_runs (.inr .unit) _ (b := unit) (tail := []) rfl
  rw [uu]
  exact hr

end AffinePin.Output

end VPVNP
end Computability
end OAI
