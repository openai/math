import OAI.Optimization.LinearProgramming.PriceGame.MarketScheduleMachine
import OAI.Optimization.LinearProgramming.PriceGame.MarketSchedulePadding
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! # Flat binary action stream for the actual transshipment state machine -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace ScheduleMachine
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

def maybeUnit (row : Plane) (i : ℕ) : List ℕ :=
  if (row.drop i).headD false then [i+1] else []

private noncomputable def maybeUnitP :
    Procedure (prodCode unaryCode planeCode) (listCode Nat.bits) (fun p => maybeUnit p.2 p.1) := by
  let ec := prodCode unaryCode planeCode
  let j := unaryToBits.comp (first unaryCode planeCode)
  let v := second unaryCode planeCode
  let bit := (listGet boolCode false).comp (j.pair v)
  let no := constant ec (listCode Nat.bits) []
  let yes := (listCons Nat.bits).comp ((successor.comp j).pair no)
  exact (conditional bit yes no).congrFun (by intro x; rfl)

/-- Zero codes a doubling; a positive integer `i + 1` codes expert `i`. -/
def rowNumbers (row : Plane) : List ℕ := 0 :: ((List.range row.length).map (maybeUnit row)).flatten

noncomputable def rowNumbersP : Procedure planeCode (listCode Nat.bits) rowNumbers := by
  let table := (tabulate ([] : List ℕ) maybeUnitP).comp ((Control.Native.rowSizeP boolCode false).pair (identity planeCode))
  let numbers := (Learning.GenerationCost.flattenP Nat.bits 0).comp table
  exact (listCons Nat.bits).comp ((constant planeCode Nat.bits 0).pair numbers)

def actionNumber {m : ℕ} : Option (Fin m) → ℕ
  | none => 0
  | some i => i.val+1

private theorem filter_singletons {α β : Type} (xs : List α) (b : α → Bool) (f : α → β) :
    (xs.map (fun x => if b x then [f x] else [])).flatten = (xs.filter b).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : b x <;> simp [h, ih]

theorem rowNumbers_correct {m : ℕ} (row : Plane) (hm : row.length = m) :
    rowNumbers row = (rowActions m row).map actionNumber := by
  have hr : (List.finRange m).map Fin.val = List.range m := by
    apply List.ext_getElem <;> simp
  unfold rowNumbers rowActions
  rw [hm, ← hr, List.map_map]
  simp only [List.map_cons, actionNumber, List.map_map]
  congr 1
  rw [← filter_singletons]
  congr 2
  funext i
  simp [maybeUnit, List.headD_eq_head?_getD, actionNumber]

private theorem planes_length (k : ℕ) (qs : List ℕ) :
    ∀ row ∈ planes k qs, row.length = qs.length := by
  induction k generalizing qs with
  | zero => simp [planes]
  | succ k ih =>
    intro row hr
    rw [planes, List.mem_append] at hr
    rcases hr with hr | hr
    · simpa using ih _ _ hr
    · rw [List.mem_singleton.mp hr]; simp

def actionStream (qs : List ℕ) : List ℕ :=
  ((planes (listCode Nat.bits qs).length qs).map rowNumbers).flatten

/-- The binary stack program emits explicit chronological double/unit actions,
including every padded zero high digit. -/
noncomputable def actionStreamP : Procedure (listCode Nat.bits) (listCode Nat.bits) actionStream :=
  (Learning.GenerationCost.flattenP Nat.bits 0).comp ((listMap [] [] rowNumbersP).comp paddedPlanesP)

theorem actionStream_correct {m : ℕ} (qty : Fin m → ℕ) :
    let qs := (List.finRange m).map qty
    actionStream qs = (Augment.schedule (listCode Nat.bits qs).length qty).map actionNumber := by
  let qs := (List.finRange m).map qty
  let k := (listCode Nat.bits qs).length
  change ((planes k qs).map rowNumbers).flatten = (Augment.schedule k qty).map actionNumber
  rw [← planes_expand k qty, List.map_flatMap]
  change ((planes k qs).map rowNumbers).flatten = ((planes k qs).map
    (fun row => (rowActions m row).map actionNumber)).flatten
  congr 1
  apply List.map_congr_left
  intro row hr
  exact rowNumbers_correct row (by simpa [qs] using planes_length k qs row hr)

/-- Out-of-range unit codes are ignored by the decoder. They cannot occur in
a stream generated from a correctly sized table. -/
def executeCode {m g : ℕ} (I : Augment.Input m g) (s : Augment.State m g) (code : ℕ) :
    Augment.State m g :=
  match code with
  | 0 => Augment.Input.double s
  | j+1 => if hj : j < m then I.unit s ⟨j,hj⟩ else s

theorem executeCode_action {m g : ℕ} (I : Augment.Input m g) (s : Augment.State m g)
    (a : Option (Fin m)) :
    executeCode I s (actionNumber a) = Augment.operation Augment.Input.double I.unit s a := by
  cases a with
  | none => rfl
  | some i => simp [executeCode, actionNumber, Augment.operation, i.isLt]

/-- Interpreting the word emitted by the finite bit program produces the actual
solver state, including the same flow and dual arrays. -/
theorem actionStream_executes {m g : ℕ} (I : Augment.Input m g) (qty : Fin m → ℕ) :
    (actionStream ((List.finRange m).map qty)).foldl (executeCode I) I.initial = I.solve qty := by
  let k := (listCode Nat.bits ((List.finRange m).map qty)).length
  have hk : Augment.Input.bits qty ≤ k := Finset.sup_le fun i _ =>
    Nat.size_le.mpr (padding_fits qty i)
  rw [actionStream_correct]
  simp only [List.foldl_map, executeCode_action]
  exact Augment.solveWithWidth_eq_of_le I qty k hk

end ScheduleMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
