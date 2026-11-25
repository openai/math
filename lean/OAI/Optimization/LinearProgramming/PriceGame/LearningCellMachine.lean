import OAI.Optimization.LinearProgramming.OracleSpec.BitStackDeployment
import OAI.Optimization.LinearProgramming.PriceGame.LearningFoldMachine
import OAI.Optimization.LinearProgramming.PriceGame.LearningCutMachine
import OAI.Optimization.LinearProgramming.PriceGame.LearningArityMachine

/-! # A uniform bit program for compiling and solving an observed cell -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram

/-- All box bounds are formed by bit instructions from the binary radius. -/
noncomputable def boxP {n : ℕ} (a : Fin n) :
    Procedure Nat.bits (matrixCode intCode n) (fun R => boxBounds R a) := by
  apply assembleMatrix
  intro s t
  if h : s = t then
    exact (Procedure.constant Nat.bits intCode 0).congrFun (by intro R; simp [boxBounds,h])
  else
    let zero := Procedure.constant Nat.bits intCode 0
    let one := Procedure.constant Nat.bits intCode 1
    let upper : Procedure Nat.bits intCode (fun R => boxUpper R a t) := by
      if ht : t = a then exact zero.congrFun (by intro R; simp [boxUpper,ht])
      else exact (Procedure.intAdd.comp (Procedure.natToInt.pair one)).congrFun (by
        intro R; simp [boxUpper,ht])
    let lower := Procedure.constant Nat.bits intCode (boxLower a s)
    exact (Procedure.intSub.comp (upper.pair lower)).congrFun (by intro R; simp [boxBounds,h])

/-- The entire actual cell learner, including processing all historical constraints and
constructing its source-averaged output. The marked option handles both reasons for rejection. -/
noncomputable def cellP {p : ℕ} (a : Fin (p+1)) :
    Procedure (prodCode Nat.bits (listCode (cutObservationCode (p+1))))
      (optionCode (vecCode ratCode (p+1)))
      (fun x : ℕ × List (Observation (p+1)) => cellRepresentative x.1 a x.2) := by
  let m := matrixCode intCode (p+1)
  let e := listCode (cutObservationCode (p+1))
  let radius := Procedure.first Nat.bits e
  let os := Procedure.second Nat.bits e
  let initial := (someP m).comp ((boxP a).comp radius)
  let folded := (foldObservationsP _ (cutThresholdP (p+1)) (cutMachine (p+1))).comp (os.pair initial)
  let solve := optionCasesP none (feasibleRepresentativeP a)
  apply (solve.comp folded).congrFun
  rintro ⟨R, observations⟩
  change (Option.elim (addObservations observations (boxBounds R a)) none (feasibleRepresentative a)) = _
  cases h : addObservations observations (boxBounds R a) with
  | none => simp [cellRepresentative,cellTable,h]
  | some c => exact feasibleRepresentative_eq a observations c h

/-- The hidden skeleton data never enter the input. The finite dimension is included as an
actual printed and read arity tag, so all sixty-six arities share one program and one clock. -/
abbrev CellInput := (p : Fin 66) × (ℕ × List (Observation (p.val+1)))

def cellInputCode : CellInput → List Bool :=
  taggedCode fun p : Fin 66 => prodCode Nat.bits (listCode (cutObservationCode (p.val+1)))

def cellAnswer (x : CellInput) : Option (List ℚ) :=
  (cellRepresentative x.2.1 (0 : Fin (x.1.val+1)) x.2.2).map List.ofFn

noncomputable def uniformCellP :
    Procedure cellInputCode (optionCode (listCode ratCode)) cellAnswer := by
  let f (p : Fin 66) (v : ℕ × List (Observation (p.val+1))) :=
    (cellRepresentative v.1 (0 : Fin (p.val+1)) v.2).map List.ofFn
  apply dispatch none (optionCode (listCode ratCode)) 66 _ f
  intro p
  apply (cellP (0 : Fin (p.val+1))).result
  intro v
  change optionCode _ (cellRepresentative v.1 0 v.2) = optionCode _ ((cellRepresentative v.1 0 v.2).map _)
  cases cellRepresentative v.1 0 v.2 <;> rfl

/-- Comparator-machine statement. The proof charges input loads, all internal work,
serialization, and halting. The cell solver performs no oracle calls. -/
theorem uniformCell_computesWithin (o : OracleSpec.WordOracle) (x : CellInput) :
    (OracleSpec.BitCode.deploy uniformCellP).ComputesWithin o (cellInputCode x)
      (3 * uniformCellP.bound.eval (cellInputCode x).length + 2 * (cellInputCode x).length + 2)
      (fun history bits => history = [] ∧ bits = optionCode (listCode ratCode) (cellAnswer x)) :=
  OracleSpec.BitCode.deploy_correct uniformCellP o x

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
