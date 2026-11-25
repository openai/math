import OAI.Hierarchy.DescentPreparedSignedTariff
import OAI.Hierarchy.DescentDatedResetPrice
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! The signed preparation, public matrix pages and all query columns at their actual pitches. -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields DescentGLNielsen
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentStaticWordColumn
open DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators
noncomputable section
variable {D cap N n r c H G K R M h l t field Ht w : ℕ} (a : Receiver D cap N n r c H G K R M h l t field Ht w)

theorem projections_bound (key : ℕ) (bits : maxBits t D cap (2^r)*M ≤ key) :
    a.projectionsBill ≤
      count (2^r) cap*(8+10*(2^key+2*(H*chunks (2^c) M)+1)+44*(H*chunks (2^c) M))+
      4+7*(count (2^r) cap*(15*(2^key+2*(H*chunks (2^c) M)+2)+91)+15) := by
  let Q:=count (2^r) cap
  let rows:=H*chunks (2^c) M
  have header (j : Fin Q) : (a.lookup j).headerWords H (2^c) M ≤ 2^key+2*rows+1 := by
    have one : (a.lookup j).loBits ≤ maxBits t D cap (2^r) :=
      word_bound a.stencil a.tapped ((column (2^r) cap).symm j)
    have price:=Nat.pow_le_pow_right (by decide : 0<2) ((Nat.mul_le_mul_right M one).trans bits)
    have padding:=DescentDyadicSpan.span_le rows
    change 2^((a.lookup j).loBits*M)+DescentDyadicSpan.span rows ≤ _
    omega
  have time (j : Fin Q) :
      4+10*(a.lookup j).headerWords H (2^c) M+(4+44*rows) ≤
      8+10*(2^key+2*rows+1)+44*rows := by have upper:=header j;omega
  have code (j : Fin Q) : 15*((a.lookup j).headerWords H (2^c) M+1)+91 ≤
      15*(2^key+2*rows+2)+91 := by have upper:=header j;omega
  have times:=Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin Q))) => time j)
  have codes:=Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin Q))) => code j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at times codes
  unfold projectionsBill
  exact Nat.add_le_add (Nat.add_le_add_right times 4) (Nat.mul_le_mul_left 7 (Nat.add_le_add_right codes 15))

def signedWords (cap H h l payload : ℕ) :=
  let depth:=(schedule (h+l)).length
  depth+depth*2^(payload/2)+6*depth*(2*((2*cap*H)*2^h+1)+2^(payload/2))

theorem signed_words (payload : ℕ)
    (shared : (h+l)*(h+l) ≤ payload/2)
    (packed : (DescentSignedCableCodec.width D cap+DescentSignedCableCodec.width D cap)*2^l ≤ payload/2) :
    a.printed ≤ signedWords cap H h l payload := by
  let depth:=(schedule (h+l)).length
  let hosts:=2*cap*H
  let b:=DescentSignedCableCodec.width D cap
  have page:=Dated.pages hosts h l b payload packed
  have keys:=Nat.pow_le_pow_right (by decide : 0<2) shared
  have top:=Nat.mul_le_mul_left (6*depth) page
  have menus:=Nat.mul_le_mul_left depth keys
  change ((a.signedOrigin+depth+depth*2^((h+l)*(h+l)))-a.signedOrigin)+
    ((a.signedChart.start+(6*depth)*2^(chartBits hosts h l b))-a.signedChart.start) ≤ _
  unfold signedWords
  change _ ≤ depth+depth*2^(payload/2)+6*depth*(2*(hosts*2^h+1)+2^(payload/2))
  omega

def retileCharge (cap N H G R M key : ℕ) :=
  let rows:=H*chunks G M
  let tables:=2*rows+R*2^key
  (8+10*tables+(2*cap*N)*(4+rows*100))+7*(15*(tables+1)+(15+(2*cap*N)*203))

theorem retile_keys (key : ℕ) (old : DescentSignedCableCodec.width D cap*(R*M) ≤ key) :
    retileBill D cap N H G R M ≤ retileCharge cap N H G R M key := by
  have price:=Nat.pow_le_pow_right (by decide : 0<2) old
  unfold retileBill retileCharge Subwords.stride
  dsimp only
  gcongr

def signedCharge (cap N H h l payload : ℕ) :=
  let sum:=N*(2*2^(payload/2))
  let page:=signedWords cap H h l payload
  let source:=1+18*N
  let depth:=(schedule (h+l)).length
  let lanes:=2*cap
  let rows:=H*2^h
  (4+10*sum)+((8+10*page)+(4+lanes*(4+rows*(2*source+4)))+
    ((4+depth*42)+(4+depth*(4+(lanes*H)*2^h*224))))+
  7*(15*(sum+1)+15*(page+2)+(15+lanes*(11+4*source))+(87+(15+depth*451)))

theorem chip_keys (payload : ℕ)
    (shared : (h+l)*(h+l) ≤ payload/2)
    (packed : (DescentSignedCableCodec.width D cap+DescentSignedCableCodec.width D cap)*2^l ≤ payload/2)
    (join : joinWidth (DescentSignedCableCodec.width D cap) N*M ≤ payload/2) :
    chipBill D cap N H M h l a.printed ≤ signedCharge cap N H h l payload := by
  have words:=a.signed_words payload shared packed
  have keys:=Nat.pow_le_pow_right (by decide : 0<2) join
  unfold chipBill signedCharge
  dsimp only
  gcongr

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
