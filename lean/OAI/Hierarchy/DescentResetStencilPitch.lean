import OAI.Hierarchy.DescentResetStencilText

namespace OAI
/-! # One numerical reset pitch fits the selected Walsh word and all dated lookup tables -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentPlainTerminal.Suffix DescentSIMDLookup DescentGLPacked DescentPackedWalsh DescentPackedColony ProtocolRAM
noncomputable section

def sharedWidth (S : StencilBook) := max (widthUnit S) (2*S.b*2^S.r)

theorem positive_width (S : StencilBook) (hb : 0<S.b) : 0<sharedWidth S :=
  (Nat.mul_pos (by omega : 0<2*S.b) (Nat.two_pow_pos _)).trans_le (Nat.le_max_right ..)

theorem pitch_inside (S : StencilBook) (h : ℕ) (hb : 0<S.b) (small : S.c≤S.m) (room : 4*sharedWidth S≤h) :
    Stencil.laneExponent S.c (sharedWidth S) h + S.r ≤ laneBits S.m h S.b := by
  let U:=sharedWidth S
  let e:=Stencil.laneExponent S.c U h
  have pu:=positive_width S hb
  have eSize:2^e≤h/(4*U):=by
    have ok:h/(4*U)≠0:=Nat.ne_of_gt (Nat.div_pos room (by omega))
    exact (Nat.pow_le_pow_right (by decide) (Nat.min_le_right ..)).trans (Nat.log2_self_le ok)
  have eBound:= (Nat.le_div_iff_mul_le (by omega : 0<4*U)).1 eSize
  have high:2^(e+S.r)*(8*S.b)≤h:=by
    rw [pow_add]
    have sr:2*S.b*2^S.r≤U:=Nat.le_max_right ..
    calc
      _ = 2^e*(4*(2*S.b*2^S.r)):=by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ sr)
      _ ≤ _ :=eBound
  have last:=Nat.le_log_of_pow_le (by decide : (1:ℕ)<2)
    ((Nat.le_div_iff_mul_le (by omega : 0<8*S.b)).2 high)
  have ec:e≤S.c:=Nat.min_le_left ..
  apply le_min
  · change e + (S.m-S.c) ≤ S.m
    omega
  · exact last

theorem coefficient (S : StencilBook) (X : StencilBook.Sources) (A : ℕ) (localBlocks : 2^S.r≤A)
    (axes : S.m≤A) (degree : S.degree≤A) (b : S.b≤A) (n : S.n≤A) (t : S.t≤A)
    (count : X.count.work≤A) (channels : S.maxPorts≤A) :
    sharedWidth S≤30*(A+1)^3 ∧
    18+128*((1+S.maxPorts)+S.m)+10*S.pageCount+S.operationCount X≤20000*(A+1)^3 := by
  let x:=2^S.r
  have one:0<A:=(Nat.two_pow_pos _).trans_le localBlocks
  have r:S.r≤A:=Nat.lt_two_pow_self.le.trans localBlocks
  have sq:S.r*x≤A*A:=Nat.mul_le_mul r localBlocks
  have bq:S.b*x≤A*A:=Nat.mul_le_mul b localBlocks
  have xx:x*x≤A*A:=Nat.mul_le_mul localBlocks localBlocks
  have xq:(S.degree+S.degree)*(2+x)≤(A+A)*(2+A):=Nat.mul_le_mul (Nat.add_le_add degree degree) (Nat.add_le_add_left localBlocks _)
  have dz:S.r*S.degree≤A*A:=Nat.mul_le_mul r degree
  have larg:=Stencil.unit_bound localBlocks axes degree n t
  have qp:Stencil.count S.r (S.degree+S.degree)≤12*(A+1)^2:=by
    rw [Stencil.count_eq];change 3+(x+S.r*x+(x*x+(S.degree+S.degree)*(2+x)))≤_
    nlinarith only [sq,xx,xq,localBlocks,one]
  have read:S.readWork X+11≤211+24*A:=by dsimp [StencilBook.readWork];omega
  have combo:=Nat.mul_le_mul qp read
  constructor
  · unfold sharedWidth widthUnit
    refine max_le (max_le (max_le ?_ ?_) ?_) ?_
    · unfold unit width
      change max (1+S.r*x+(1+S.r*x)) (1+S.r*x+S.b*x) ≤ _
      apply max_le <;> nlinarith only [sq,bq,Nat.zero_le (A^3)]
    · change S.b*x ≤ _
      nlinarith only [bq,Nat.zero_le (A^3)]
    · nlinarith only [larg,Nat.zero_le (A^2),Nat.zero_le A]
    · change 2*S.b*x ≤ _
      nlinarith only [bq,Nat.zero_le (A^3)]
  · unfold StencilBook.pageCount StencilBook.operationCount
    rw [S.socket_count]
    change 18+128*((1+S.maxPorts)+S.m)+10*(40+2*(S.degree+4+5*S.r)+(1+(x+S.r*x)+x^2)+(S.m+1)+_)+
      (64+4*S.r+S.r*(2*(25+56*S.degree)+4)+2*Stencil.count S.r (S.degree+S.degree)*(S.readWork X+11))≤_
    nlinarith only [combo,qp,sq,xx,dz,localBlocks,axes,degree,channels,r,one,Nat.zero_le (A^3)]

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
