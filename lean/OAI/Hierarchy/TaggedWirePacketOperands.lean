import OAI.Hierarchy.ProtocolRAMScan
import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordGeometry

namespace OAI
/-! # Primitive native fields for an ordered local packet -/
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Fin.CommRing
variable {n S m W : ℕ}

/-- The row ID and its two physical endpoint words are the only reads per hop.
A direct wire takes its primary. A two-radius wire also takes its mate. -/
structure Operands (len : Fin n→ℕ) where
  oldSite : Fin n→Bool→Expr
  width : Fin n→Expr
  edge : (i : Fin n)→Fin (len i)→Expr
  endSite : (i : Fin n)→Fin (len i)→Bool→Expr

variable (old : Fin n→Chord S) (edge : Fin m→Chord S) (route : Fin n→List (Fin m))
    (bits : Fin n→ℕ) (o : Operands fun i=>(route i).length) (mem : Memory W) (row : Word W)

structure Reads : Prop where
  oldLo : ∀i,(o.oldSite i false).eval mem row=((old i).1.1.val : Word W)
  oldHi : ∀i,(o.oldSite i true).eval mem row=((old i).1.2.val : Word W)
  width : ∀i,(o.width i).eval mem row=(bits i : Word W)
  key : ∀i q,(o.edge i q).eval mem row=(((route i).get q).val : Word W)
  low : ∀i q,(o.endSite i q false).eval mem row=((edge ((route i).get q)).1.1.val : Word W)
  high : ∀i q,(o.endSite i q true).eval mem row=((edge ((route i).get q)).1.2.val : Word W)

end Hierarchy.WireTelescope.PacketTurns

end OAI
