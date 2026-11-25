import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCostComplete

/-! # Passing an actual historical feature table to the compact learner

The support is a list on the tape. Its length determines the printed arity tag, capped at
the uniform maximum for unrestricted input. Its canonical length for a real skeleton is
already at most 65.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram

abbrev generatorPayloadCode := prodCode Nat.bits (listCode (listCode ratCode))

def arityOfRoots (roots : List ℕ) : Fin 66 := ⟨min roots.length 65,by omega⟩

def generatorParameters (x : List ℕ × (ℕ × List (List ℚ))) : GenerationCost.GeneratorInput :=
  ⟨arityOfRoots x.1,x.2⟩

private noncomputable def asWord {α : Type} (e : α → List Bool) : Procedure e id e :=
  (Procedure.identity e).result (fun _ => rfl)

/-- Write the actual arity tag, then the existing radius and row payload. -/
noncomputable def generatorParametersP :
    Procedure (prodCode (listCode Nat.bits) generatorPayloadCode) GenerationCost.generatorInputCode
      generatorParameters := by
  let env := prodCode (listCode Nat.bits) generatorPayloadCode
  let roots := Procedure.first (listCode Nat.bits) generatorPayloadCode
  let payload := Procedure.second (listCode Nat.bits) generatorPayloadCode
  let len := (GenerationCost.lengthUnaryP Nat.bits 0).comp roots
  let small := Procedure.binaryLe.comp ((Procedure.unaryToBits.comp len).pair (Procedure.constant env Nat.bits 65))
  let arity : Procedure env unaryCode (fun x => min x.1.length 65) :=
    (Procedure.conditional small len (Procedure.constant env unaryCode 65)).congrFun (by
      intro x; simp [min_def])
  let tag := (asWord unaryCode).comp arity
  let payloadBits := (asWord generatorPayloadCode).comp payload
  let separated := ((Procedure.prepend (id : List Bool → List Bool) [false]).comp payloadBits).result
    (ec := id) (h := fun x : List ℕ × (ℕ × List (List ℚ)) => false :: generatorPayloadCode x.2) (fun _ => rfl)
  exact (Procedure.append.comp (tag.pair separated)).result (fun _ => rfl)

/-- Invoke the single verified cell-generator bit program after forming its public arity argument. -/
noncomputable def generatorFromRootsP :
    Procedure (prodCode (listCode Nat.bits) generatorPayloadCode) (listCode (listCode ratCode))
      (fun x => GenerationCost.generatorAnswer (generatorParameters x)) :=
  GenerationCost.uniformGenerateP.comp generatorParametersP

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
