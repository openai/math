import OAI.Hierarchy.DescentResetSuffixFee

namespace OAI
/-! Pricing the Walsh endpoint writer at the receiver's actual batch. -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentPlainTerminal.Suffix DescentSIMDLookup DescentGLPacked DescentPackedWalsh DescentPackedColony ProtocolRAM
noncomputable section

theorem headers_at_chosen (S : StencilBook) (h : ℕ) (live : 0<S.M)
    (width : sharedWidth S*S.M≤h/2) (cutoff : S.levels+S.total≤h/2) : StencilBook.Widths S h := by
  let shared:=sharedWidth S
  have reserved:widthUnit S≤ shared:=Nat.le_max_left ..
  have one:1≤S.M:=live
  have paid (n) (p:n≤ shared) : n*S.M≤h/2 := (Nat.mul_le_mul_right _ p).trans width
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

theorem writer_at_chosen (S : StencilBook) (X : StencilBook.Sources) (h A base out f B K g cap Y w : ℕ)
    (live : 0<S.M) (rows : 0<S.rows) (width : sharedWidth S*S.M≤h/2) (cutoff : S.levels+S.total≤h/2)
    (blocks : 2^S.r≤A) (dimension : S.m≤A) (degree : S.degree≤A) (b : S.b≤A)
    (n : S.n≤A) (t : S.t≤A) (work : X.count.work≤A) (channels : S.maxPorts≤A) :
    paidTime S X base out f B g + 7*DescentStaticWordColumn.names (paidProgram S X base out f B K g cap Y w) ≤
      580000*(A+1)^3*S.units h := by
  let T:=10*S.pageCount+S.operationCount X
  have span:=S.installed_span h base (headers_at_chosen S h live width cutoff)
  have lits:=S.literal_le_span X base out (32*Nat.clog 2 (2*S.degree)) (2^(f+1)*B)
  have stored:S.literalWords base out X (32*Nat.clog 2 (2*S.degree)) (2^(f+1)*B)≤S.pageCount*S.units h:=by omega
  have printed:=Nat.mul_le_mul_left 10 stored
  have row:1+S.rows≤S.units h:=by
    exact (Nat.add_le_add_right (Nat.le_add_right 1 S.hosts) S.rows).trans (Nat.le_add_right ..)
  have loop:=Nat.mul_le_mul_right (S.operationCount X) row
  have native:=S.paid_time X base out f B g
  have op:paidTime S X base out f B g≤T*S.units h:=by
    dsimp only [T];nlinarith only [printed,loop,native]
  have fee:=(coefficient S X A blocks dimension degree b n t work channels).2
  have coefficientFit:T≤20000*(A+1)^3:=by dsimp [T];omega
  have clocks:=op.trans (Nat.mul_le_mul_right _ coefficientFit)
  have text:DescentStaticWordColumn.names (paidProgram S X base out f B K g cap Y w) ≤
    4*paidTime S X base out f B g := (paid_text S X base out f B K g cap Y w rows).size
  nlinarith only [clocks,text]

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
