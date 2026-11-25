import Mathlib.Tactic

namespace OAI
/-! # The physical reset prelude's polynomial in the measured counts -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup

/-- The degree is fixed once the round and its public maximum degree are chosen. -/
def canvasCoeff (D : ℕ) := 1000000*(D+1)^2*(4^(Nat.clog 2 D)+1)

def account (H D m y r c page pitch sm walsh₁ walsh₂ insert : ℕ) :=
  let n:=H*(m+1)+H*D
  let input:=m*(3*page+walsh₁+walsh₂)+(4*n+3*(n*y))+H
  let tables:=(D*r+1)*(2*insert)+(D+4)*pitch
  let depth:=((4+H*(8+2*(1+7)))+(4+H*(8+2*(1+9*m))))+m*(4+H*(8+2*(13+2*(37*sm))))
  let time:=(4+18*(H*y)+(4+10*input))+(8+10*tables)+
    ((8+D*(4+H*y*(2*(1+18*(r*c))+4))+D*(4+H*y*(2*(7+121*D)+4)))+((m*(4+90*(H*y))+4)+((4+32*H)+depth))+
      ((12+780*n)+(4+100*(n*y))+((4+48*n)+(4+48*n))))
  let text:=39+15*(input+1)+15*(tables+2)+
    (((15+D*(11+4*(1+18*(r*c))))+(15+D*(11+4*(7+121*D))))+(19+183*m)+(11+4*14)+4*depth+3*(11+4*128)+(11+4*48)+2*(11+4*22))
  time+7*text

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1800000 in
theorem polynomials (H D m y r c sm Q : ℕ) (host : 0<H) (rows : 0<y) (radix : 0<r) :
    account H D m y r c (4*(H*y)) (4*(H*y)) sm Q Q Q ≤
      1000000*(D+1)^2*(sm+1)*((m+1)*(r*(c+1))*(H*y)+(m+1)*r*Q) :=by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero host.ne'
  obtain ⟨b,rfl⟩:=Nat.exists_eq_succ_of_ne_zero rows.ne'
  obtain ⟨e,rfl⟩:=Nat.exists_eq_succ_of_ne_zero radix.ne'
  unfold account
  simp only [Nat.succ_eq_add_one]
  ring_nf
  omega

end Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup

end OAI
