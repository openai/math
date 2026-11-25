import OAI.Hierarchy.DescentResetStencilPitch

namespace OAI
/-! # Bit invoice of the physical re-packing and terminal-cell computation -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentPlainTerminal.Suffix DescentSIMDLookup DescentGLPacked DescentPackedWalsh DescentPackedColony
open DescentColonies.CandidateRAM ProtocolRAM
noncomputable section

/-- Combined cost of the issued two procedures, at the batch size selected from
the measured Walsh precision and the true local terminal encoding. -/
theorem suffix_fee (S : StencilBook) (X : StencilBook.Sources) (chip : Bank)
    (first base out f B K g cap Y h w ratio A : ℕ) (hb : 0<S.b) (rows : 0<S.rows)
    (small : S.c≤S.m) (wide : 4*sharedWidth S≤h) (cutoff : S.levels+S.total≤h/2)
    (batch : S.M=2^Stencil.laneExponent S.c (sharedWidth S) h)
    (blocks : 2^S.r≤A) (axes : S.m≤A) (degree : S.degree≤A) (b : S.b≤A)
    (n : S.n≤A) (t : S.t≤A) (count : X.count.work≤A) (channels : S.maxPorts≤A)
    (hardware : w≤ratio*h) {K₀ : ℕ}
    (alignment : 2^S.c=K₀*(2^(laneBits S.m h S.b-S.r-Stencil.laneExponent S.c (sharedWidth S) h)*S.M)) :
    let e:=Stencil.laneExponent S.c (sharedWidth S) h
    let R:=laneBits S.m h S.b-S.r-e
    let positive:=show 0<S.M by rw [batch];exact Nat.two_pow_pos _
    let repack:=repackProgram S chip first (2^R) alignment (Nat.two_pow_pos _) positive w
    let paid:=paidProgram S X base out f B K g cap Y w
    let clock:=repackTime S chip first (2^R) alignment (Nat.two_pow_pos _) positive+paidTime S X base out f B g
    (clock+7*DescentStaticWordColumn.names (repack.seq paid))*w ≤
      580000*ratio*(A+1)^3*(h+2*S.hosts*h+8*S.hosts*2^S.c*(30*(A+1)^3)+2^(h/2)*h) := by
  let U:=sharedWidth S
  let e:=Stencil.laneExponent S.c U h
  let old:=laneBits S.m h S.b
  let R:=old-S.r-e
  let pos:0<S.M:=by rw [batch];exact Nat.two_pow_pos _
  let rt:=repackTime S chip first (2^R) alignment (Nat.two_pow_pos _) pos
  let pt:=paidTime S X base out f B g
  let rcode:=repackProgram S chip first (2^R) alignment (Nat.two_pow_pos _) pos w
  let pcode:=paidProgram S X base out f B K g cap Y w
  change (rt+pt+7*DescentStaticWordColumn.names (rcode.seq pcode))*w≤_
  have inside:e+S.r≤old:=pitch_inside S h hb small wide
  have aligned:S.r+R+e=old:=by dsimp [R];omega
  have upos:=positive_width S hb
  have area:8*S.b≤h:=by
    have q:2*S.b≤U:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos S.r)).trans (Nat.le_max_right ..)
    omega
  obtain ⟨localWidth,cost⟩:=coefficient S X A blocks axes degree b n t count channels
  have rprice:=repack_tariff S chip first (2^R) R old h w ratio U alignment rfl (Nat.two_pow_pos _) pos
    upos wide batch hb (keys_fit hb area) aligned hardware
  have rooms:=headers_at_pitch S h U (Nat.le_max_left ..) upos wide batch cutoff
  have price:=S.tariff X h w ratio base out f B g U rooms upos wide hardware batch
  let world:=h+2*S.hosts*h+8*S.hosts*2^S.c*U+2^(h/2)*h
  have RW:h+S.hosts*h+8*S.hosts*2^S.c*U+2^(h/2)*h≤world:=by
    dsimp only [world]
    rw [Nat.mul_assoc 2 S.hosts h]
    omega
  have rprice' : rt*w≤ratio*(18+128*((1+S.maxPorts)+S.m))*world := rprice.trans (Nat.mul_le_mul_left _ RW)
  have pprice' : pt*w≤ratio*(10*S.pageCount+S.operationCount X)*world := price
  have priced:(rt+pt)*w≤ratio*(20000*(A+1)^3)*world:=calc
    _ ≤ ratio*(18+128*((1+S.maxPorts)+S.m))*world+ratio*(10*S.pageCount+S.operationCount X)*world:=by
      rw [Nat.add_mul];exact Nat.add_le_add rprice' pprice'
    _ = ratio*(18+128*((1+S.maxPorts)+S.m)+10*S.pageCount+S.operationCount X)*world:=by ring
    _ ≤ _:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cost)
  have textBound:=seq_bound (repack_text S chip first (2^R) w alignment (Nat.two_pow_pos _) pos rows)
    (paid_text S X base out f B K g cap Y w rows)
  have words:DescentStaticWordColumn.names (rcode.seq pcode)≤4*(rt+pt):=textBound.size
  calc
    _ ≤ (29*(rt+pt))*w:=Nat.mul_le_mul_right _ (by omega)
    _ ≤ 29*(ratio*(20000*(A+1)^3)*world):=by rw [Nat.mul_assoc];exact Nat.mul_le_mul_left _ priced
    _ = (580000*ratio*(A+1)^3)*world:=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ (by dsimp only [world];gcongr)

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
