import OAI.Optimization.LinearProgramming.Lattice.BitProbeTags

/-! The literal transition between maximum-coordinate queries. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

def nextMaxArgCode := prodCode maxBaseCode intRowCode

noncomputable def nextMaxP : Procedure nextMaxArgCode actionCode
    (fun x : (Params × IntMatrix) × Row => nextMax x.1.1 x.1.2 x.2) := by
  let base := first maxBaseCode intRowCode
  let z := (first paramsCode intMatrixCode).comp base
  let todo := (second paramsCode intMatrixCode).comp base
  let best := second maxBaseCode intRowCode
  let zeroCarry := rightP carryLeftCode (leftP ratioCode (z.pair best))
  let onNil := askP (negateRowP.comp best) zeroCarry
  let a := (listHead (ea:=intRowCode) ([]:Row)).comp todo
  let tail := (listTail (ea:=intRowCode)).comp todo
  let onCons := askP a
    (leftP carryRightCode (leftP maxCode ((z.pair tail).pair (a.pair best))))
  refine (conditional ((emptyListP intRowCode).comp todo) onNil onCons).congrFun ?_
  rintro ⟨⟨z,rows⟩,best⟩
  cases rows <;> rfl

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
