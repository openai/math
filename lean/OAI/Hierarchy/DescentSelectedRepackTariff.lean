import OAI.Hierarchy.DescentResetRepackTariff
import OAI.Hierarchy.DescentResetRemixTariff

namespace OAI
/-! # The physical return from wide Walsh words to the selected receiver pitch -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentPlainTerminal.Suffix DescentSIMDLookup DescentGLPacked DescentPackedWalsh DescentPackedColony ProtocolRAM
noncomputable section

/-- The selector table and the true machine loop have different sizes. Every
source Walsh word is paid once by the common dyadic key, and the unpacked
return visits one row for each selected receiver word. -/
theorem repack_selected (S : StencilBook) (chip : Bank) (first e R old h w : ℕ)
    {groups : ℕ} (factor : 2^S.c=groups*(2^R*S.M))
    (batch : S.M=2^e) (hb : 0<S.b) (word : bigKey old S.b≤h/2)
    (aligned : S.r+R+e=old) (present : 0<S.rows) :
    let pos:=show 0<S.M by rw [batch];exact Nat.two_pow_pos _
    let proc:=repackProgram S chip first (2^R) factor (Nat.two_pow_pos _) pos w
    let fee:=repackTime S chip first (2^R) factor (Nat.two_pow_pos _) pos
    fee+7*DescentStaticWordColumn.names proc ≤
        29*(8+128*(((1+S.maxPorts)+S.m)*S.rows)+10*2^(h/2)) := by
  let a:=S.b*2^S.r
  let channels:=(1+S.maxPorts)+S.m
  let H:=channels*S.hosts
  have pos:0<S.M:=by rw [batch];exact Nat.two_pow_pos _
  have order : R≤old:=by omega
  have cost : R≤S.b*2^old:=(order.trans Nat.lt_two_pow_self.le).trans (Nat.le_mul_of_pos_left _ hb)
  have key : a*(2^R*2^e)=S.b*2^old:=by dsimp only [a];rw [←aligned,pow_add,pow_add];ring
  have table : 2^R*Subwords.stride a (2^R) S.M≤2^(h/2):=by
    rw [batch]
    apply Subwords.dictionary_budget a h R e
    rw [key]
    unfold bigKey at word
    rw [Nat.add_mul] at word
    omega
  let fee:=repackTime S chip first (2^R) factor (Nat.two_pow_pos _) pos
  let proc:=repackProgram S chip first (2^R) factor (Nat.two_pow_pos _) pos w
  have visits:=Subwords.invoice (w:=0) first H a factor (Nat.two_pow_pos _) pos chip
  change fee≤8+128*(H*chunks (2^S.c) S.M)+10*(2^R*Subwords.stride a (2^R) S.M) at visits
  have count : H*chunks (2^S.c) S.M=channels*S.rows:=by simp only [H,StencilBook.rows,Nat.mul_assoc]
  rw [count] at visits
  have ticks : fee≤8+128*(channels*S.rows)+10*2^(h/2):=by omega
  have code : DescentStaticWordColumn.names proc≤4*fee:=
    (repack_text S chip first (2^R) w factor (Nat.two_pow_pos _) pos present).size
  calc
    fee + 7*DescentStaticWordColumn.names proc ≤ fee+7*(4*fee) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ code) _
    _ = 29*fee := by ring
    _ ≤ _ := Nat.mul_le_mul_left 29 ticks

/-- Multiply by the actual machine width only after the table text and every
visit have been paid. The group count and receiver batch both stay in rows. -/
theorem repack_at_pitch (S : StencilBook) (chip : Bank) (first e h w : ℕ)
    {groups : ℕ} (factor : 2^S.c=groups*(2^(laneBits S.m h S.b-S.r-e)*S.M))
    (batch : S.M=2^e) (hb : 0<S.b) (oldArea : 8*S.b≤h)
    (inside : e+S.r≤laneBits S.m h S.b) (present : 0<S.rows) :
    let R:=laneBits S.m h S.b-S.r-e
    let pos:=show 0<S.M by rw [batch];exact Nat.two_pow_pos _
    (repackTime S chip first (2^R) factor (Nat.two_pow_pos _) pos+
      7*DescentStaticWordColumn.names (repackProgram S chip first (2^R) factor (Nat.two_pow_pos _) pos w))*w ≤
      29*(8+128*(((1+S.maxPorts)+S.m)*(S.hosts*chunks (2^S.c) S.M))+10*2^(h/2))*w := by
  have align : S.r+(laneBits S.m h S.b-S.r-e)+e=laneBits S.m h S.b:=by omega
  exact Nat.mul_le_mul_right _ (repack_selected S chip first e _ _ h w factor batch hb (keys_fit hb oldArea) align present)

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

namespace Hierarchy.DescentSixParty
open DescentPlainTerminal.Suffix DescentGLPacked.BankImage DescentGLPacked.BankImage.Dated ProtocolRAM
theorem remix_same_pitch {D : ℕ} (P : StencilBook) (M : ℕ) (C : Chart) (base solve fresh : ℕ)
    (counts : Bank) (pair : Fin D→Bank) (h w : ℕ) (hb : 0<P.b) :
    remixInvoice {P with M:=M} C base solve fresh counts pair h w hb=
      remixInvoice P C base solve fresh counts pair h w hb:=rfl
end Hierarchy.DescentSixParty

end OAI
