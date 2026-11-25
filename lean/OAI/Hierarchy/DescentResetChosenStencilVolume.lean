import OAI.Hierarchy.DescentResetSelectedStencilWriter
import OAI.Hierarchy.DescentSelectedRepackTariff
import OAI.Hierarchy.DescentResetDateStencil

namespace OAI
/-! One actual selected Walsh phase. Its front retains its original radix and
its two endpoint passes visit exactly the receiving chart's true packed rows. -/
namespace Hierarchy.DescentSixParty.PackedFlow.ResetMiddle
open DescentPackedWalsh DescentSIMDLookup DescentPlainTerminal.Suffix ProtocolRAM DescentStaticWordColumn
open PackedFlow.Padded
noncomputable section
set_option quotPrecheck false
variable (P : ResetMiddle)
local notation "S" => P.S
local notation "rows" => (S).rows
local notation "units" h:arg => (S).units h

private theorem repack_at_record (book : StencilBook) (chip : Bank) (first e h w ratio groups : ℕ)
    (factor : 2^book.c=groups*(ratio*book.M)) (pos : 0<ratio) (live : 0<book.M)
    (eqn : ratio=2^(laneBits book.m h book.b-book.r-e))
    (batch : book.M=2^e) (hb : 0<book.b) (word : 8*book.b≤h)
    (inside : e+book.r≤laneBits book.m h book.b) (present : 0<book.rows) :
    (repackTime book chip first ratio factor pos live+7*names (repackProgram book chip first ratio factor pos live w))*w ≤
      29*(8+128*(((1+book.maxPorts)+book.m)*(book.hosts*chunks (2^book.c) book.M))+10*2^(h/2))*w := by
  subst ratio
  exact repack_at_pitch book chip first e h w factor batch hb word inside present

theorem chosen_clock (e h w A : ℕ) (head : P.high=(S).high) (low : P.low=laneBits (S).m h (S).b)
    (batch : (S).M=2^e) (ratio : P.ratio=2^(laneBits (S).m h (S).b-(S).r-e))
    (word : 8*(S).b≤h) (inside : e+(S).r≤laneBits (S).m h (S).b) (present : 0<rows)
    (width : sharedWidth (S)*(S).M≤h/2) (cutoff : (S).levels+(S).total≤h/2)
    (blocks : 2^(S).r≤A) (dimension : (S).m≤A) (degree : (S).degree≤A) (bits : (S).b≤A)
    (small : (S).n≤A) (targets : (S).t≤A) (cost : P.X.count.work≤A) (channels : (S).maxPorts≤A) :
    (P.time w+7*names (P.code w))*w ≤
      remixInvoice (S) P.chart P.origin P.solve P.fresh P.counts P.peers h w P.positive+
      (1200000*(A+1)^3*((S).hosts+rows+(h+1)^3*2^(h/2)))*w := by
  let T := (S).hosts+rows+(h+1)^3*2^(h/2)
  have one:1≤T:=by dsimp [T];omega
  have paidRows:rows≤T:=by dsimp [T];omega
  have table:2^(h/2)≤(h+1)^3*2^(h/2):=Nat.le_mul_of_pos_left _ (by positivity)
  have tableFit:2^(h/2)≤T:=by dsimp [T];omega
  have extent:units h≤2*T:=by dsimp [StencilBook.units,T];omega
  have writer:=writer_at_chosen (S) P.X h A P.base P.bank P.f P.B P.K P.g P.cap P.Y w
    P.batchPos present width cutoff blocks dimension degree bits small targets cost channels
  have writerCost:=Nat.mul_le_mul_right w (writer.trans (Nat.mul_le_mul_left _ extent))
  have repack:=repack_at_record (S) P.chip P.first e h w P.ratio P.groups P.factor P.ratioPos P.batchPos
    ratio batch P.positive word inside present
  have times:=Nat.mul_le_mul_left ((1+(S).maxPorts)+(S).m) paidRows
  have lanes:29*(8+128*(((1+(S).maxPorts)+(S).m)*rows)+10*2^(h/2)) ≤
      (29*(18+128*((1+(S).maxPorts)+(S).m)))*T := by
    nlinarith only [times,one,tableFit]
  have repackCost:=repack.trans (Nat.mul_le_mul_right w lanes)
  have scales:29*(18+128*((1+(S).maxPorts)+(S).m))+2*(580000*(A+1)^3) ≤ 1200000*(A+1)^3 := by
    nlinarith only [dimension,channels,Nat.zero_le (A^2),Nat.zero_le (A^3)]
  have both:=Nat.mul_le_mul_right w (Nat.mul_le_mul_right T scales)
  have native : (P.time w+7*names (P.code w))*w =
      remixInvoice (S) P.chart P.origin P.solve P.fresh P.counts P.peers h w P.positive+
      (repackTime (S) P.chip P.first P.ratio P.factor P.ratioPos P.batchPos+
        7*names (repackProgram (S) P.chip P.first P.ratio P.factor P.ratioPos P.batchPos w))*w+
      (paidTime (S) P.X P.base P.bank P.f P.B P.g+
        7*names (paidProgram (S) P.X P.base P.bank P.f P.B P.K P.g P.cap P.Y w))*w := by
    unfold time code remixInvoice
    simp only [names_seq,head,low]
    ring
  rw [native]
  change _≤_+(1200000*(A+1)^3*T)*w
  nlinarith only [repackCost,writerCost,both]

end
end Hierarchy.DescentSixParty.PackedFlow.ResetMiddle

end OAI
