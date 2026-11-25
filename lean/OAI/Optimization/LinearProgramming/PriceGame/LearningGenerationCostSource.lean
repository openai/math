import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCostComplete
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCostOrdering
import OAI.Optimization.LinearProgramming.PriceGame.LearningOrderingReference

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace GenerationCost

open ExactQuantumFactoring.BitStackProgram

/-- Every candidate, including rejected ones, occurs at the same index in both
enumerations. The noncomputable reference ordering has therefore been compiled. -/
theorem historicalCodes_eq {n cap : ℕ} (s : Experts.Feature n → Finset ℚ) (h : n*n ≤ cap) :
    historicalCodes cap (historyRows s) = (Experts.codes s).map serializeCell := by
  rw [Experts.codes_eq_pi]
  exact (reference_pi_cartesian s h).symm

/-- Equality of the actual ordered expert lists. The indices can be used
unchanged by the fixed-share weights, score arrays, and trial traces. -/
theorem generateWire_eq_generate {p R : ℕ} (a : Fin (p+1)) (hp : p ≤ 65)
    (s : Experts.Feature (p+1) → Finset ℚ) :
    generateWire (66*66) R a (historyRows s) = Experts.generate R a s := by
  have hcap : (p+1)*(p+1) ≤ 66*66 := Nat.mul_le_mul (by omega) (by omega)
  unfold generateWire Experts.generate
  rw [historicalCodes_eq s hcap, List.filterMap_map]
  apply congrArg (fun k => (Experts.codes s).filterMap k)
  funext code
  exact congrArg (cellRepresentative R a) (observe_serializeCell s code)

/-- The arity-uniform deployed bit machine writes the exact original expert
list, including the order of experts and the coordinates of each vector. -/
theorem sourceGenerator_computesWithin (o : OracleSpec.WordOracle) (p : Fin 66) (R : ℕ)
    (s : Experts.Feature (p.val+1) → Finset ℚ) :
    let x : GeneratorInput := ⟨p,R,historyRows s⟩
    (OracleSpec.BitCode.deploy uniformGenerateP).ComputesWithin o (generatorInputCode x)
      (3 * uniformGenerateP.bound.eval (generatorInputCode x).length + 2 * (generatorInputCode x).length + 2)
      (fun history bits => history = [] ∧ bits =
        listCode (listCode ratCode) ((Experts.generate R (0 : Fin (p.val+1)) s).map List.ofFn)) := by
  let x : GeneratorInput := ⟨p,R,historyRows s⟩
  have hx : generatorAnswer x = (Experts.generate R (0 : Fin (p.val+1)) s).map List.ofFn := by
    exact congrArg (List.map List.ofFn) (generateWire_eq_generate _ (by omega : p.val ≤ 65) s)
  simpa only [hx] using uniformGenerate_computesWithin o x

end GenerationCost
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
