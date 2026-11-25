import OAI.Optimization.LinearProgramming.Lattice.BitProbeMaximum

/-! Finite stack instructions for starting, orienting, and comparing probe rows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

noncomputable def startP : Procedure paramsCode actionCode start := by
  let sz := first (prodCode unaryCode unaryCode) intMatrixCode
  let p := (first unaryCode unaryCode).comp sz
  let rows := second (prodCode unaryCode unaryCode) intMatrixCode
  let remain := (listReverse (ea:=intRowCode) ([]:Row)).comp rows
  exact nextMaxP.comp (((identity paramsCode).pair remain).pair ((replicateP intCode 0).comp p))

noncomputable def orientP (answer : Bool) : Procedure maxCode actionCode (orient answer) := by
  let base := first maxBaseCode rowPairCode
  let rows := second maxBaseCode rowPairCode
  let a := (first intRowCode intRowCode).comp rows
  let best := (second intRowCode intRowCode).comp rows
  let oriented : Procedure maxCode intRowCode
      (fun s : MaxState => if answer then s.2.1 else s.2.1.map Neg.neg) := by
    cases answer
    · exact negateRowP.comp a
    · exact a
  let both := oriented.pair best
  exact askP (rowDifferenceP.comp both) (leftP carryRightCode (rightP maxCode (base.pair both)))

noncomputable def compareP (answer : Bool) : Procedure maxCode actionCode (compare answer) := by
  let base := first maxBaseCode rowPairCode
  let rows := second maxBaseCode rowPairCode
  let best : Procedure maxCode intRowCode
      (fun s : MaxState => if answer then s.2.1 else s.2.2) := by
    cases answer
    · exact (second intRowCode intRowCode).comp rows
    · exact (first intRowCode intRowCode).comp rows
  exact nextMaxP.comp (base.pair best)

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
