import Mathlib.Algebra.Order.Field.Rat

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market

variable {E G : Type*}

/-- An expert's bid on a real arc, or zero for its dummy arc. -/
def bid (c : E → G → ℚ) (e : E) : Option G → ℚ
  | none => 0
  | some i => c e i

end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
