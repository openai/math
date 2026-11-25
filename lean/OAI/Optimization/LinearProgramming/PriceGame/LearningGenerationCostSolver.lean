import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCostObservations
import OAI.Optimization.LinearProgramming.PriceGame.LearningPathMachine

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace GenerationCost

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- Present values enter the result as one item; absent values enter as zero items. -/
private noncomputable def optListP {α : Type} (ea : α → List Bool) :
    Procedure (BitMachine.optionCode ea) (listCode ea) Option.toList := by
  let one := (listCons ea).comp ((identity ea).pair (constant ea (listCode ea) []))
  let dispatch := casesSum (constant emptyCode (listCode ea) []) one
  let asSum : Option α → Unit ⊕ α := fun x => match x with | none => .inl () | some a => .inr a
  let p := (dispatch.precompose asSum).congrEncoding
    (ec := BitMachine.optionCode ea) (ed := listCode ea) (by intro x; cases x <;> rfl) (fun _ => rfl)
  exact p.congrFun (by intro x; cases x <;> rfl)

private theorem flatten_optLists {α : Type} (xs : List (Option α)) :
    (xs.map Option.toList).flatten = xs.filterMap id := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases a <;> simp [ih]

/-- Remove rejected candidates while copying every surviving framed result. -/
noncomputable def compactOptionsP {α : Type} (ea : α → List Bool) (da : α) :
    Procedure (listCode (BitMachine.optionCode ea)) (listCode ea) (List.filterMap id) :=
  ((flattenP ea da).comp (listMap none [] (optListP ea))).congrFun flatten_optLists

/-- The concrete list produced by the bit program; `rows` is a sequence of
historical thresholds in the fixed feature order. -/
def generateWire {p : ℕ} (cap : ℕ) (R : ℕ) (a : Fin (p+1)) (rows : List (List ℚ)) :
    List (Fin (p+1) → ℚ) :=
  (historicalCodes cap rows).filterMap (fun c => cellRepresentative R a
    (observe (FinEnum.toList (Experts.Feature (p+1))) (c, rows)))

/-- Compose every binary-machine stage with the supplied compiled cell solver.
The input radius and threshold history stay available to each call. -/
noncomputable def generateWireUsingP {p : ℕ} (cap : ℕ) (a : Fin (p+1))
    (solve : Procedure (prodCode Nat.bits (listCode (BitMachine.cutObservationCode (p+1))))
      (BitMachine.optionCode (BitMachine.vecCode ratCode (p+1)))
      (fun x : ℕ × List (Observation (p+1)) => cellRepresentative x.1 a x.2)) :
    Procedure (prodCode Nat.bits (listCode (listCode ratCode))) (listCode (BitMachine.vecCode ratCode (p+1)))
      (fun x : ℕ × List (List ℚ) => generateWire cap x.1 a x.2) := by
  let ec := listCode (rawCellCode ratCode)
  let eh := listCode (listCode ratCode)
  let ctx := prodCode Nat.bits eh
  let ew := BitMachine.vecCode ratCode (p+1)
  let candidate := first ec ctx
  let rest := second ec ctx
  let r := (first Nat.bits eh).comp rest
  let rows := second Nat.bits eh
  let cuts := (observeP (FinEnum.toList (Experts.Feature (p+1)))).comp (candidate.pair (rows.comp rest))
  let runOne := solve.comp (r.pair cuts)
  let runAll := mapContextP [] none runOne
  let enumerated := (historicalCodesP ratCode 0 cap).comp rows
  let v := runAll.comp (enumerated.pair (identity ctx))
  exact ((compactOptionsP ew (fun _ => 0)).comp v).congrFun (by
    intro x; simp only [Function.comp_apply, id_eq, List.filterMap_map, generateWire])

theorem generateWire_contains {p R : ℕ} (a : Fin (p+1)) (hp : p ≤ 65)
    (s : Experts.Feature (p+1) → Finset ℚ) {v : Fin (p+1) → ℚ} (hv : v ∈ Experts.generate R a s) :
    v ∈ generateWire (66*66) R a (historyRows s) := by
  obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp hv
  exact List.mem_filterMap.mpr ⟨serializeCell c, source_cap_covers hp s c, by
    simpa only [observe_serializeCell] using hc⟩

theorem length_generateWire {p : ℕ} (cap R : ℕ) (a : Fin (p+1)) (history : List (List ℚ)) :
    (generateWire cap R a history).length ≤ ((history.take cap).map (fun r => 2*r.length+1)).prod :=
  (List.length_filterMap_le _ _).trans_eq (length_historicalCodes cap history)

end GenerationCost
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
