import OAI.Hierarchy.DescentExteriorProposals
import OAI.Hierarchy.DescentGLPrefix

namespace OAI
/-! # The exterior witnesses in both physical chunk orders -/
namespace Hierarchy.DescentExterior
open DescentGL

/-- The same wire is a destination bit of one phase and a source bit of the next. -/
abbrev Hidden (e j r t : ℕ) := (Bool × Fin e × Plane j r) × Fin t

abbrev Column (e j r : ℕ) := Bool × Bool × Fin e × Rows j r

theorem header_price (e j r t : ℕ) :
    Fintype.card (Column e j r)=4*(e*2^(j+r)) ∧
    Fintype.card (Hidden e j r t)=2*(e*2^(j+(j+r))*t) := by
  constructor <;> simp [Column,Hidden,Plane,Rows,pow_add] <;> ring

end Hierarchy.DescentExterior

end OAI
