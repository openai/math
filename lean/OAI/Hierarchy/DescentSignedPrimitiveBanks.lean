import OAI.Hierarchy.DescentSignedPrefix
import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! Static public rows and dyadic bank shapes used by the original ordinary compiler. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentDyadicSpan Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
abbrev job:=SignedPrefix.Job
def lit {N:ℕ} (book:Fin N→DescentOrdinaryAtomFieldRAM.ROM.Page) (bits:ℕ):job:=
  .words (N*2^bits) (DescentOrdinaryAtomFieldRAM.ROM.contents book bits)
def col (n rows:ℕ) (e:ℕ→Expr):job:=.columns n rows (span rows) e
def subbank (base rows index:ℕ):Bank:=⟨base+index*span rows,Nat.clog 2 rows⟩
def fromIndex {n:ℕ} (f:Fin n→Expr) (j:ℕ):Expr:=if h:j<n then f ⟨j,h⟩ else .lit 0
end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
