import OAI.Optimization.LinearProgramming.NormalSubspace.Main
import OAI.Optimization.LinearProgramming.PriceGame.ExtremalSign
import OAI.Optimization.LinearProgramming.Compression.ServiceTheorem

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

theorem normal_decision : Nonempty Spec :=
  normal_decision_of_primitives PriceGame.extremalSignRecovery Compression.onlineMinorCompression

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
