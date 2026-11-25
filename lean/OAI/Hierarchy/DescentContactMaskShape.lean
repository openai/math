import OAI.Hierarchy.DescentContactDonorShape

namespace OAI
/-! # Post-trunk count of all positive contact sockets at original hosts -/
namespace Hierarchy.DescentContactMaskShape
open DescentSIMDLookup DescentContactDonorFront DescentResetCandidateDate
def donors (a : DescentContactDonorFront.Shape) := a.lows*(2*a.cap)
def sockets (a : DescentContactDonorFront.Shape) :=
  let roots:=2^(a.residual+1)+2^(a.residual+1)*(2^a.n+1)
  2*(roots*(2^a.n+2^a.height))
def rowSpan (a : DescentContactDonorFront.Shape) :=2^Nat.clog 2 (a.hosts*chunks a.groups a.batch)
def date (a : DescentContactDonorFront.Shape) (base : ℕ) : DescentResetCandidateDate.Shape:=
  ⟨base+sockets a*rowSpan a,sockets a,a.batch,a.hosts,a.groups⟩
def massEnd (a : DescentContactDonorFront.Shape) (base : ℕ) :=
  (date a base).endAddress (donors a+1) a.fieldBits

def directionSize (a : DescentContactDonorFront.Shape) := 2*2^(a.fieldBits*a.batch)
def endAddress (a : DescentContactDonorFront.Shape) (base : ℕ) := massEnd a base+directionSize a

theorem translate (a : DescentContactDonorFront.Shape) (base : ℕ) : endAddress a base=base+endAddress a 0 := by
  simp [endAddress,massEnd,date,DescentResetCandidateDate.Shape.endAddress,DescentResetCandidateDate.Shape.base,
    DescentResetCandidateDate.Shape.scratch,DescentResetCandidateDate.Shape.size,DescentResetCandidateDate.Shape.width,
    DescentResetCandidateDate.Shape.stride,DescentResetCandidateDate.Shape.rowBits,DescentResetCandidateDate.Shape.rows,Nat.add_assoc]

theorem prior (a : DescentContactDonorFront.Shape) (base : ℕ) : base≤endAddress a base:=by rw [translate];omega

theorem donor_arity (a : DescentContactDonorFront.Shape) : donors a+1≤a.boardFields:=by
  let r:=((a.residual+1)*2^a.residual)*(2^a.n+1)
  have pos:r>0:=by dsimp [r];positivity
  have rank:0<r*((a.degree+1)*r):=Nat.mul_pos pos (Nat.mul_pos (Nat.zero_lt_succ _) pos)
  change a.lows*(2*a.cap)+1≤
    a.lows+a.degree*a.lows+a.lows*(2*a.cap)+(a.lows*a.lows+a.degree*(a.degree*6))+r*((a.degree+1)*r)
  omega

end Hierarchy.DescentContactMaskShape

end OAI
