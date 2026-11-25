import OAI.Hierarchy.DescentResetCandidateShape

namespace OAI
/-! # Numeric footprint of old signed donors, reciprocal lanes, and relative-neighbor ranks -/
namespace Hierarchy.DescentContactDonorFront
open DescentSIMDLookup
structure Shape where
  hosts : ℕ
  groups : ℕ
  batch : ℕ
  degree : ℕ
  lows : ℕ
  cap : ℕ
  n : ℕ
  residual : ℕ
  height : ℕ
  fieldBits : ℕ
  queryBits : ℕ
  cargoBits : ℕ

namespace Shape
variable (A : Shape)

def boardFields :=
  let r:=A.residual
  let rows:=((r+1)*2^r)*(2^A.n+1)
  (A.lows+A.degree*A.lows+A.lows*(2*A.cap)+(A.lows*A.lows+A.degree*(A.degree*6)))+
    rows*((A.degree+1)*rows)
def returnFields := 1+((A.degree*(2*A.cap))*2+A.degree*A.degree)
def laneFields := 2*((A.lows*(2*A.cap))*3)
private def calendar (first jobs : ℕ) : DescentResetCandidateDate.Shape :=
  ⟨first,jobs,A.batch,A.hosts,A.groups⟩
def senderEnd (base : ℕ) :=
  let fields:=A.fieldBits
  let lanes:=A.laneFields
  let jobs:=(A.lows*(2*A.cap))*2
  let first:=A.calendar base 1
  let split:=A.calendar (first.endAddress A.boardFields fields+lanes*first.stride) lanes
  let left:=A.calendar (split.endAddress 2 (fields*lanes)) jobs
  let right:=A.calendar (left.endAddress A.returnFields fields) jobs
  right.endAddress A.returnFields fields
def idCells := 1+2^Nat.clog 2 A.hosts
def haloCells :=
  let R:=A.hosts*chunks A.groups A.batch
  let D:=A.degree+1
  let q:=A.queryBits
  let b:=A.cargoBits
  let M:=A.batch
  3*2^Nat.clog 2 (A.hosts*D)+2*2^(A.fieldBits*M)+
    (2^(q*M)+(D*2^(q*M+b)+(2^(b*M)+(2^((b+b)*M)+R))))+2^Nat.clog 2 (R+1)
def endAddress (base : ℕ) := (A.senderEnd base+A.idCells)+A.haloCells

theorem translate (base : ℕ) : A.endAddress base=base+A.endAddress 0 := by
  simp [endAddress,senderEnd,calendar,DescentResetCandidateDate.Shape.endAddress,
    DescentResetCandidateDate.Shape.base,DescentResetCandidateDate.Shape.scratch,
    DescentResetCandidateDate.Shape.size,DescentResetCandidateDate.Shape.width,
    DescentResetCandidateDate.Shape.stride,DescentResetCandidateDate.Shape.rowBits,
    DescentResetCandidateDate.Shape.rows,Nat.add_assoc]
end Shape
end Hierarchy.DescentContactDonorFront

end OAI
