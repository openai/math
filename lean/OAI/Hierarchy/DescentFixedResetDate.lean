import OAI.Hierarchy.DescentEnteredPhysicalReset

namespace OAI
/-! # Fixed reset instructions from their public address and table descriptions -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {a : PhysicalReset} {base w : ℕ}

theorem DateInputs.same {u v : a.DateInputs base w}
    (shape : u.shape=v.shape) (count : u.count=v.count) (hub : u.hub=v.hub) (src : u.src=v.src)
    (groups : u.g=v.g) (y : u.Y=v.Y) (rows : u.sourceRows=v.sourceRows)
    (oldDegree : u.oldDegree=v.oldDegree) (roots : u.roots=v.roots) (atlas : u.atlas=v.atlas)
    (earlier : u.earlier=v.earlier) (number : u.number=v.number) (directory : u.directory=v.directory)
    (menu : HEq u.menu v.menu) (degree : u.degree=v.degree) : u=v :=by
  cases u
  cases v
  cases shape
  cases count
  cases hub
  cases src
  cases groups
  cases y
  cases rows
  cases oldDegree
  cases roots
  cases atlas
  cases earlier
  cases number
  cases directory
  cases eq_of_heq menu
  cases degree
  rfl

theorem FinalInputs.same {u : a.DateInputs base w} {b c : u.FinalInputs}
    (table : b.menu=c.menu) (origin : b.previousRoleBase=c.previousRoleBase)
    (stride : b.previousRoleStride=c.previousRoleStride) (bits : b.previousRoleBits=c.previousRoleBits)
    (prior : b.io=c.io) : b=c :=by
  cases b
  cases c
  cases table
  cases origin
  cases stride
  cases bits
  cases prior
  rfl

variable (L : DescentResetCanvasIngress.Layout) (floor : ℕ)
    (blocks : a.k=L.k) (ports : a.c=2*L.cap)
local notation "ready" => atIngress L floor a blocks ports

/-- The entire public reset with ingress, survivor and operand tables, private
roles and census has one piece of code and one clock for a fixed date. -/
theorem entered_same {u v : (ready).DateInputs (L.endAddress floor) w}
    {b : u.FinalInputs} {c : v.FinalInputs}
    (inputs : u=v) (table : b.menu=c.menu) (origin : b.previousRoleBase=c.previousRoleBase)
    (stride : b.previousRoleStride=c.previousRoleStride) (bits : b.previousRoleBits=c.previousRoleBits)
    (prior : b.io=c.io) (hub : Bank) (atom : Fin (2^L.k)→Expr) (wire : L.signed.Slot→Bank) :
    entered L floor blocks ports u b hub atom wire=entered L floor blocks ports v c hub atom wire :=by
  cases inputs
  cases FinalInputs.same table origin stride bits prior
  rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
