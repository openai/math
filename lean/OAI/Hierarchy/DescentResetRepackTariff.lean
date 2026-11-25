import OAI.Hierarchy.DescentResetStencilTariff
import OAI.Hierarchy.DescentPackedWalshPrice

namespace OAI
/-! # Repacking price at the actual old Walsh pitch and the new kernel pitch -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentPlainTerminal.Suffix DescentSIMDLookup DescentGLPacked DescentPackedWalsh DescentPackedColony ProtocolRAM
noncomputable section

/-- A common kernel width accounts for the census, weight, and signed output tables. -/
def widthUnit (S : StencilBook) :=
  max (max (unit S.r S.b) (S.b*2^S.r)) (Stencil.stencilUnit S.r S.m S.degree S.n S.t)

theorem headers_at_pitch (S : StencilBook) (h shared : ℕ) (reserved : widthUnit S≤ shared)
    (positive : 0<shared) (wide : 4*shared≤h) (batch : S.M=2^Stencil.laneExponent S.c shared h)
    (cutoff : S.levels+S.total≤h/2) : StencilBook.Widths S h := by
  let m:=S.M
  have fit:(shared+shared)*S.M≤h/2:=by rw [batch];exact lane_fit _ _ _ positive wide
  have one:1≤S.M:=by rw [batch];exact Nat.two_pow_pos _
  have paid (n) (p:n≤ shared) : n*S.M≤h/2 :=
    (Nat.mul_le_mul_right _ (p.trans (Nat.le_add_right ..))).trans fit
  have bounds:=max_le_iff.mp reserved
  have pp:=max_le_iff.mp bounds.1
  have fieldBounds:=max_le_iff.mp bounds.2
  have shape:=max_le_iff.mp fieldBounds.2
  have tail:=max_le_iff.mp shape.2
  have n:S.n≤ shared:=((Nat.le_add_left ..).trans fieldBounds.1)
  have c:S.n≤h/2:=(Nat.le_mul_of_pos_right _ one).trans (paid _ n)
  have bits:2^S.r*S.m≤ shared:=by nlinarith only [shape.1,Nat.zero_le (2^S.r)]
  refine ⟨paid _ pp.1,cutoff,?_,?_,paid _ fieldBounds.1⟩
  · dsimp [Stencil.ReaderTables.largest]
    exact max_le c (max_le (paid _ pp.2) (max_le (paid _ tail.2) (by exact paid _ bits)))
  · apply paid
    nlinarith only [shape.1]

theorem repack_tariff (S : StencilBook) (chip : Bank) (first ratio R₀ oldExp h w K shared : ℕ)
    {K₀ : ℕ} (factor : 2^S.c=K₀*(ratio*S.M)) (rat : ratio=2^R₀) (ratioPos : 0<ratio) (pos : 0<S.M)
    (positive : 0<shared) (big : 4*shared≤h) (batch : S.M=2^Stencil.laneExponent S.c shared h)
    (oldWidth : 0<S.b) (wordArea : bigKey oldExp S.b≤h/2)
    (aligned : S.r+R₀+Stencil.laneExponent S.c shared h=oldExp) (hw : w≤K*h) :
    repackTime S chip first ratio factor ratioPos pos*w ≤
      K*(18+128*((1+S.maxPorts)+S.m))*(h+S.hosts*h+8*S.hosts*2^S.c*shared+2^(h/2)*h) := by
  let channels:=(1+S.maxPorts)+S.m
  let H:=channels*S.hosts
  let e:=Stencil.laneExponent S.c shared h
  let a:=S.b*2^S.r
  have high:=Subwords.invoice (w:=0) first H a factor ratioPos pos chip
  have scale:a*(2^R₀*2^e)=S.b*2^oldExp:=by dsimp [a,e];rw [←aligned,pow_add,pow_add];ring
  have sub:R₀≤S.b*2^oldExp := by
    have p:R₀≤oldExp:=by omega
    have q:oldExp≤2^oldExp:=Nat.lt_two_pow_self.le
    exact (p.trans q).trans (Nat.le_mul_of_pos_left _ oldWidth)
  have fit:R₀+a*(2^R₀*2^e)≤h/2:=by rw [scale];unfold bigKey at wordArea;rw [Nat.add_mul] at wordArea;omega
  have table:ratio*Subwords.stride a ratio S.M≤2^(h/2):=by rw [rat,batch];exact Subwords.dictionary_budget a h R₀ e fit
  have rows:S.rows*h≤S.hosts*h+8*S.hosts*2^S.c*shared:=by
    rw [StencilBook.rows,batch,(Stencil.pitch S.c S.r shared h).2.2]
    simpa only [Stencil.laneExponent,one_mul] using (charged S.hosts S.c shared h h 1 positive big (by omega))
  let X:=repackTime S chip first ratio factor ratioPos pos
  have invoice:X≤8+128*(channels*S.rows)+10*2^(h/2):=by
    change X≤8+128*(H*chunks (2^S.c) S.M)+10*(ratio*Subwords.stride a ratio S.M) at high
    have num:(H*chunks (2^S.c) S.M)=channels*S.rows:=by simp only [H,StencilBook.rows,Nat.mul_assoc]
    rw [num] at high
    omega
  have y:=Nat.mul_le_mul invoice hw
  have c:=Nat.mul_le_mul_left (K*(128*channels)) rows
  change X*w≤_
  change X*w≤K*(18+128*channels)*(h+S.hosts*h+8*S.hosts*2^S.c*shared+2^(h/2)*h)
  nlinarith only [y,c,Nat.zero_le (K*S.hosts*h),Nat.zero_le (K*8*S.hosts*2^S.c*shared),
    Nat.zero_le (K*channels*h),Nat.zero_le (K*h),Nat.zero_le (K*channels*2^(h/2)*h),Nat.zero_le (K*2^(h/2)*h)]

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
