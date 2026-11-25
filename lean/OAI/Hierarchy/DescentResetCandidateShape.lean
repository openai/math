import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Addresses of a packed reset-candidate table and its output rows -/
namespace Hierarchy.DescentResetCandidateDate
open DescentSIMDLookup
structure Shape where
  first : ℕ
  jobs : ℕ
  lanes : ℕ
  hosts : ℕ
  groups : ℕ

variable {N field b w : ℕ}
namespace Shape
variable (L : Shape)
def rows := L.hosts*chunks L.groups L.lanes
def rowBits := Nat.clog 2 L.rows
def stride := 2^L.rowBits
def width (N field : ℕ) := max ((field*N+field)*L.lanes) L.rowBits
def size (N field : ℕ) := (N*2+2)*2^(L.width N field)
def scratch (N field : ℕ) := L.first+L.size N field
def base (N field : ℕ) := L.scratch N field+L.stride
def endAddress (N field : ℕ) := L.base N field+L.jobs*L.stride

def costBound (N field limit : ℕ) := 4+10*L.size N field+
  (4+L.jobs*(4+L.rows*(2*limit+4)+(4+44*L.rows)))

def nameBound (N field limit : ℕ) := 15*(L.size N field+1)+(15+L.jobs*(102+4*limit))

end Shape
end Hierarchy.DescentResetCandidateDate

end OAI
