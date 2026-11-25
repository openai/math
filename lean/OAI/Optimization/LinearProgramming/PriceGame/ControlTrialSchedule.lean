import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialCore
import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryTraces
import Mathlib.Data.List.OfFn

/-! Move from a chronological snoc transcript to the first-order loop which consumes
the schedule one call at a time. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open TrialExecution
variable {N : ℕ} {α Pkt I C R : Type}

/-- The effects of the child and its feedback are separate segments of the same
chronological transcript. -/
def RefinesStep (ops : Kernel I Pkt R C PackedQuery) (calls fuel : ℕ) (input : I)
    (rows : List C) (tr : List (PackedQuery × Bool)) (c : C) : Prop :=
  let prep := ops.prepare input rows
  ∃ left middle returned, tr = left++middle ∧
    Evaluates ops calls (.node fuel (ops.childInput input prep)) left returned ∧
    Scan (ops.finish input rows prep returned) [] middle c

/-- A reference prefix already executed can be prepended to the remaining raw loop,
without recomputing any completed call or reordering its designated questions. -/
theorem ScheduleTrace.prepend {P : (j : ℕ) → (Fin j → α) → α → Prop}
    {step : ∀ j xs, Computation N {y // P j xs y}}
    (ops : Kernel I Pkt R C PackedQuery) (calls fuel : ℕ) (input : I) (encode : α → C)
    (href : ∀ j xs c tr, Emits (step j xs) tr c →
      RefinesStep ops calls fuel input (List.ofFn (fun i => encode (xs i))) tr (encode c.val))
    {j tr xs} (s : ScheduleTrace P step j tr xs) :
    ∀ {rem tail result}, Evaluates ops calls (.rounds fuel rem input (List.ofFn fun i => encode (xs.val i)))
        tail result →
      Evaluates ops calls (.rounds fuel (j+rem) input []) (tr++tail) result := by
  induction s with
  | nil =>
    intro rem tail result rest
    simpa using rest
  | @snoc n tr pre xs x old last ih =>
    intro rem tail result rest
    obtain ⟨left,middle,returned,rfl,hchild,hscan⟩ := href n xs.val x tr last
    have eq : List.ofFn (fun i => encode ((snocSchedule P xs x).val i)) =
        (List.ofFn fun i => encode (xs.val i)) ++ [encode x.val] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      simp [snocSchedule]
    rw [eq] at rest
    have h := ih (Evaluates.call hchild hscan rest)
    simpa only [Nat.succ_add, Nat.add_succ, List.append_assoc] using h

theorem runSchedule_evaluates {P : (j : ℕ) → (Fin j → α) → α → Prop}
    {step : ∀ j xs, Computation N {y // P j xs y}}
    (ops : Kernel I Pkt R C PackedQuery) (calls fuel : ℕ) (input : I) (encode : α → C)
    (href : ∀ j xs c tr, Emits (step j xs) tr c →
      RefinesStep ops calls fuel input (List.ofFn (fun i => encode (xs i))) tr (encode c.val))
    {tr xs} (e : Emits (runSchedule P step calls) tr xs) :
    Evaluates ops calls (.rounds fuel calls input []) tr (ops.assemble input (List.ofFn fun i => encode (xs.val i))) := by
  have s := scheduleTrace_of_emits P step calls e
  simpa using s.prepend ops calls fuel input encode href (Evaluates.done fuel input _)

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
