import OAI.Optimization.LinearProgramming.Lattice.BitBirdDetFormula
import OAI.Optimization.LinearProgramming.Lattice.BitBirdGrowth

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
open ExactQuantumFactoring.BitStackProgram

/-- A single bit-stack program computes the integer determinant of every encoded square matrix;
the polynomial intermediate word bound is proved for arbitrary, even ragged, input lists. -/
noncomputable def listDetP : Procedure intMatrixCode intCode listDet :=
  listDetWithGrowthP birdIterationBound birdUpdate_word_growth

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
