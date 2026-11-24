import OAI.Computability.VPVNP.RankQueryStackSchur
import Mathlib.Data.Fin.VecNotation

/-!
# Numeric query registers for the Schur coefficient machine

The first register selects a query tag. The other five hold indices and degrees.
Power and factor convolution queries share the same row, column, exponent and
degree positions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.SchurKey

variable {n U Z : ℕ}

/-- Six numeric fields of the current scalar query, including its tag. -/
def words : K n U Z → Fin 6 → ℕ
  | .product d b u z => ![0, d.val, b.start, b.count, u.val, z.val]
  | .factor a u z => ![1, a.val, 0, 0, u.val, z.val]
  | .outer a h i j z => ![2, a.val, i.val, j.val, h.val, z.val]
  | .inner a h i j z => ![3, a.val, i.val, j.val, h.val, z.val]
  | .power a q => ![4, a.val, q.row.val, q.col.val, q.exponent.val, q.degree.val]
  | .scalar neg i j z => ![5, i.val, j.val, neg.toNat, 0, z.val]
  | .one => ![6, 0, 0, 0, 0, 0]

end RankQuery.Stack.SchurKey

end VPVNP
end Computability
end OAI
