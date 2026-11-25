import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCostSolver
import OAI.Optimization.LinearProgramming.PriceGame.LearningCellMachine

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace GenerationCost

open ExactQuantumFactoring.BitStackProgram

/-- Unconditional finite binary-stack implementation of one skeleton's entire
historical expert list: cell enumeration, rational comparisons, compilation
of constraints, Floyd–Warshall, source averaging, and discarding failed cells. -/
noncomputable def generateWireP {p : ℕ} (a : Fin (p+1)) :
    Procedure (prodCode Nat.bits (listCode (listCode ratCode))) (listCode (BitMachine.vecCode ratCode (p+1)))
      (fun x : ℕ × List (List ℚ) => generateWire (66*66) x.1 a x.2) :=
  generateWireUsingP (66*66) a (BitMachine.cellP a)

/-- In particular, the exact source-rooted representative used by the adaptive
shrinking-width proof appears in the list written by this program. -/
theorem generateWire_selected {p R : ℕ} {a : Fin (p+1)} (hp : p ≤ 65)
    {s : Experts.Feature (p+1) → Finset ℚ} {v : Fin (p+1) → ℚ} {t : Paths.Table (p+1)}
    (ht : cellTable R a (Experts.trueObservations s v) = some t) :
    representative (Paths.read t) a ∈ generateWire (66*66) R a (historyRows s) :=
  generateWire_contains a hp s (Experts.trueTable_selected_mem_generate ht)

/-- Arity, radius, and lists of observed rational thresholds. -/
abbrev GeneratorInput := (_p : Fin 66) × (ℕ × List (List ℚ))

def generatorInputCode : GeneratorInput → List Bool :=
  BitMachine.taggedCode fun _ : Fin 66 => prodCode Nat.bits (listCode (listCode ratCode))

def generatorAnswer (x : GeneratorInput) : List (List ℚ) :=
  (generateWire (66*66) x.2.1 (0 : Fin (x.1.val+1)) x.2.2).map List.ofFn

private theorem listCode_vec {n : ℕ} (xs : List (Fin n → ℚ)) :
    listCode (BitMachine.vecCode ratCode n) xs = listCode (listCode ratCode) (xs.map List.ofFn) := by
  induction xs with
  | nil => rfl
  | cons v xs ih => simp [listCode,BitMachine.vecCode,ih]

/-- One program and one polynomial for all allowed skeleton arities, with
the arity read from the input tape. -/
noncomputable def uniformGenerateP :
    Procedure generatorInputCode (listCode (listCode ratCode)) generatorAnswer := by
  let f (p : Fin 66) (s : ℕ × List (List ℚ)) :=
    (generateWire (66*66) s.1 (0 : Fin (p.val+1)) s.2).map List.ofFn
  apply BitMachine.dispatch [] (listCode (listCode ratCode)) 66 _ f
  intro p
  apply (generateWireP (0 : Fin (p.val+1))).result
  intro x
  exact listCode_vec _

/-- A complete comparator-machine trace, including the output and halting step. -/
theorem uniformGenerate_computesWithin (o : OracleSpec.WordOracle) (x : GeneratorInput) :
    (OracleSpec.BitCode.deploy uniformGenerateP).ComputesWithin o (generatorInputCode x)
      (3 * uniformGenerateP.bound.eval (generatorInputCode x).length + 2 * (generatorInputCode x).length + 2)
      (fun history bits => history = [] ∧ bits = listCode (listCode ratCode) (generatorAnswer x)) :=
  OracleSpec.BitCode.deploy_correct uniformGenerateP o x

end GenerationCost
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
