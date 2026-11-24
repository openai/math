import OAI.Computability.VPVNP.RAMTapeSortCompare
import OAI.Computability.VPVNP.RAMTapeSortRowProgram
import OAI.Computability.VPVNP.StructuredStackRuns

/-!
# Executing a comparator at a local or cross-site sorting row

The selected source determines which physical stream supplies the right
record. Verification consumes the outgoing copy. Selection prepends the
chosen record in reverse bit order to the next block, and both operations
push their validity bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRow

open RAMBoundary Boundary

/-- The comparator starts with w unary width markers and empty width scratch, saved operand
buffers and selection staging. -/
structure CompareReady (w : ℕ) (s : Stacks Port) : Prop where
  width : s .width = List.replicate w true
  widthBack : s .widthBack = []
  savedLeft : s .savedLeft = []
  savedRight : s .savedRight = []
  selectTmp : s .selectTmp = []

/-- The caller retains the unread part of both operands. -/
def compareResult (s : Stacks Port) (src : RightSource) (lt rt chunk : List Bool) (flag : Bool) :
    Stacks Port := fun p =>
  if p = .left then lt else if p = src.port then rt else if p = .next then chunk ++ s .next else
    if p = .flags then flag :: s .flags else s p

private def bank (s : Stacks Port) (lt rt : List Bool) : Sorter.Bank :=
  ⟨lt, rt, [], [], [], [], [], s .next, s .flags⟩

private theorem lift_compare {w n : ℕ} (r : FiniteRoutine Sorter.Port) (src : RightSource)
    (s : Stacks Port) (a b : RawSlot w) (lt rt chunk : List Bool) (flag : Bool) (ready : CompareReady w s)
    (hl : s .left = recordBytes a ++ lt) (hr : s src.port = recordBytes b ++ rt)
    (run : r.Runs n (Sorter.ready a b (bank s lt rt)).stacks
      (Sorter.returned w (bank s lt rt) flag chunk).stacks) :
    (r.onPorts (comparePorts src)).Runs n s (compareResult s src lt rt chunk flag) := by
  obtain ⟨hw, hwb, hsl, hsr, ht⟩ := ready
  apply FiniteRoutine.runs_onPorts_framed r (comparePorts_injective src) run
  · intro p
    cases p <;> first | rfl | assumption
  · intro p
    cases src <;> cases p <;> first | rfl | assumption
  · intro p h
    have h₁ : p ≠ .left := Ne.symm (h .left)
    have h₂ : p ≠ src.port := Ne.symm (h .right)
    have h₃ : p ≠ .next := Ne.symm (h .next)
    have h₄ : p ≠ .flags := Ne.symm (h .valid)
    simp only [compareResult, h₁, h₂, h₃, h₄, ite_false]

/-- Verify a cross-site send against the local slot, retaining its unread tail. -/
theorem verify_runs {w : ℕ} (s : Stacks Port) (a b : RawSlot w) (lt rt : List Bool)
    (ready : CompareReady w s) (hl : s .left = recordBytes a ++ lt)
    (hr : s .crossSend = recordBytes b ++ rt) :
    verify.Runs (50*w+18) s (compareResult s .outgoing lt rt [] (verifyOK a b)) :=
  lift_compare Sorter.verify .outgoing s a b lt rt [] (verifyOK a b) ready hl hr
    (Sorter.verify_runs a b (bank s lt rt))

/-- Execute a known comparator orientation on two prepared operand streams. -/
theorem select_runs {w : ℕ} (src : RightSource) (s : Stacks Port) (keepMin : Bool) (a b : RawSlot w)
    (lt rt : List Bool) (ready : CompareReady w s) (hl : s .left = recordBytes a ++ lt)
    (hr : s src.port = recordBytes b ++ rt) :
    (select src keepMin).Runs (65*w+19) s
      (compareResult s src lt rt (recordBytes (chosen keepMin a b)).reverse (selectOK a b)) :=
  lift_compare (Sorter.select keepMin) src s a b lt rt (recordBytes (chosen keepMin a b)).reverse
    (selectOK a b) ready hl hr (Sorter.select_runs keepMin a b (bank s lt rt))

/-- Reading the public orientation takes one instruction before selection. -/
theorem oriented_runs {w : ℕ} (src : RightSource) (s : Stacks Port) (keepMin : Bool) (a b : RawSlot w)
    (lt rt : List Bool) (ready : CompareReady w s) (hkeep : s .orientation = [keepMin])
    (hl : s .left = recordBytes a ++ lt) (hr : s src.port = recordBytes b ++ rt) :
    (oriented src).Runs (65*w+20) s (compareResult (Function.update s .orientation []) src lt rt
      (recordBytes (chosen keepMin a b)).reverse (selectOK a b)) := by
  let t := Function.update s .orientation []
  have ht : CompareReady w t :=
    ⟨ready.width, ready.widthBack, ready.savedLeft, ready.savedRight, ready.selectTmp⟩
  have hr' : t src.port = recordBytes b ++ rt := by cases src <;> exact hr
  have hs := select_runs src t keepMin a b lt rt ht hl hr'
  cases keepMin with
  | false => exact Routine.runs_popCase_false Port.orientation _ _ _ hkeep hs
  | true => exact Routine.runs_popCase_true Port.orientation _ _ _ hkeep hs

end RAMTape.SortRow

end VPVNP
end Computability
end OAI
