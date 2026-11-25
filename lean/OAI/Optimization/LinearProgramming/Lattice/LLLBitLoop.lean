import OAI.Optimization.LinearProgramming.Lattice.LLLBitSweep

/-! The fixed outer indexed LLL loop. Its two branches first perform the complete column
sweep and then use the actual integer Lovász test. A halted cursor is absorbing. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec.Fuel

variable {S I : Type}

abbrev OuterState (S : Type) := ℕ × (ℕ × S)

def outerCode (es : S → List Bool) := prodCode unaryCode (prodCode Nat.bits es)

def advanceOrSwap (accept : ℕ × S → Bool) (swap : ℕ × S → S) (c : ℕ × S) : ℕ × S :=
  if accept c then (c.1+1,c.2) else (max (c.1-1) 1, swap c)

noncomputable def advanceOrSwapP {es : S → List Bool} {accept : ℕ × S → Bool} {swap : ℕ × S → S}
    (test : Procedure (prodCode Nat.bits es) boolCode accept)
    (exchange : Procedure (prodCode Nat.bits es) es swap) :
    Procedure (prodCode Nat.bits es) (prodCode Nat.bits es) (advanceOrSwap accept swap) := by
  let raw := identity (prodCode Nat.bits es)
  let cursor := first Nat.bits es
  let state := second Nat.bits es
  let one := constant (prodCode Nat.bits es) Nat.bits 1
  let succ := binaryAdd.comp (cursor.pair one)
  let prev := binarySub.comp (cursor.pair one)
  let leastOne := (choose prev one).comp ((binaryZero.comp prev).pair raw)
  refine (((choose (leastOne.pair exchange) (succ.pair state)).comp (test.pair raw)).congrFun ?_)
  intro c
  change (if accept c then (c.1+1,c.2) else (if decide (c.1-1=0) then 1 else c.1-1, swap c)) = _
  unfold advanceOrSwap
  split
  · rfl
  · congr 1
    by_cases h : c.1-1=0
    · simp [h]
    · simp [h, max_eq_left (show 1 ≤ c.1-1 by omega)]

def outerStep (active : ℕ × S → Bool) (sweep : OuterState S → S)
    (accept : ℕ × S → Bool) (swap : ℕ × S → S) (x : OuterState S) : OuterState S :=
  if active x.2 then (x.1,advanceOrSwap accept swap (x.2.1,sweep x)) else x

noncomputable def outerStepP {es : S → List Bool} {active : ℕ × S → Bool}
    {sweep : OuterState S → S} {accept : ℕ × S → Bool} {swap : ℕ × S → S}
    (running : Procedure (prodCode Nat.bits es) boolCode active)
    (reduce : Procedure (outerCode es) es sweep)
    (test : Procedure (prodCode Nat.bits es) boolCode accept)
    (exchange : Procedure (prodCode Nat.bits es) es swap) :
    Procedure (outerCode es) (outerCode es) (outerStep active sweep accept swap) := by
  let cap := first unaryCode (prodCode Nat.bits es)
  let frame := second unaryCode (prodCode Nat.bits es)
  let row := (first Nat.bits es).comp frame
  let branch := (advanceOrSwapP test exchange).comp (row.pair reduce)
  let update := cap.pair branch
  let original := identity (outerCode es)
  exact ((choose original update).comp ((running.comp frame).pair original))

/-- The work cap is included in the frame passed to each nested sweep. A second guard
compares the entire outer frame with the corresponding bound, including its unary cap. -/
noncomputable def runOuter (ei : I → List Bool) (es : S → List Bool) (init : I → S)
    (step : OuterState S → OuterState S) (time space : Polynomial ℕ) (a : I) : S :=
  let len := (ei a).length
  let cap := space.eval len
  (((cappedTransition (outerCode es) step)^[time.eval len]
    ((Polynomial.C 4 * space + 4).eval len, cap, 1, init a)).2).2.2

noncomputable def runOuterP {ei : I → List Bool} {es : S → List Bool} {init : I → S}
    {step : OuterState S → OuterState S} (start : Procedure ei es init)
    (next : Procedure (outerCode es) (outerCode es) step) (time space : Polynomial ℕ) :
    Procedure ei es (runOuter ei es init step time space) := by
  let initial := (clock ei space).pair ((constant ei Nat.bits 1).pair start)
  let loop := cappedIterationP initial next time (Polynomial.C 4 * space + 4)
  let cursor := (second unaryCode (prodCode Nat.bits es)).comp loop
  exact (second Nat.bits es).comp cursor

/-- Space correctness of the capped outer controller is required only for the specifically
initialized native trajectory. Arbitrary raw states are always covered by its fixed clock. -/
theorem runOuter_exact (ei : I → List Bool) (es : S → List Bool) (init : I → S)
    (step : OuterState S → OuterState S) (time space : Polynomial ℕ) (a : I)
    (hfit : ∀ i, 0 < i → i ≤ time.eval (ei a).length →
      (outerCode es ((step^[i]) (space.eval (ei a).length, 1, init a))).length ≤
        (Polynomial.C 4 * space + 4).eval (ei a).length) :
    runOuter ei es init step time space a = ((step^[time.eval (ei a).length])
      (space.eval (ei a).length, 1, init a)).2.2 := by
  dsimp only [runOuter]
  rw [cappedTransition_iterate_exact (hfit := hfit)]

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
