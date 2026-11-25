import OAI.Hierarchy.DescentMatchLaneNumbers
import OAI.Hierarchy.DescentCensusLaneNumbers
import OAI.Hierarchy.DescentDonorLaneNumbers

namespace OAI
/-! # The installed donor lane also holds the ordinary matcher's actual tables -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentPackedColony DescentRawCablePanel DescentRawCablePanel.DepotRAM
noncomputable section

/-- The packed output has enough fields for the actual input whenever the raw
cable cap is positive. Both use the same digit width. -/
theorem shape_inputs_fit {r D cap profile : ℕ} (live : 0<r) (wires : 0<cap) :
    let s:=shape r D (2*cap) profile
    s.inputBits≤ s.outputBits := by
  let bins:=binCount r D
  let entries:=entryCount r D (2*cap)
  have binsPos : 0<bins := by dsimp [bins,binCount];omega
  have enough : r*bins≤entries := Nat.le_mul_of_pos_right (r*bins) (by omega)
  have oldRows : r≤entries := (Nat.le_mul_of_pos_right r binsPos).trans enough
  have oldBins : bins≤entries := (Nat.le_mul_of_pos_left bins live).trans enough
  have pairs : entries≤r*entries := Nat.le_mul_of_pos_left _ live
  dsimp only
  apply Nat.mul_le_mul_left
  change r+(bins+(entries*3+(entries*3+r*entries)))≤1+(r*entries)*12
  omega

/-- Both the stored mark/address panel and every key of the output/profile
lookup fit the existing donor field. No conversion of its packed lane count is needed. -/
theorem matching_widths (f : DepotRAM.Shape) (k colors board u : ℕ)
    (rows : f.blocks=2^k) (cap : 0<f.cap) (boardFit : board≤2^k)
    (digit : k+3≤f.short)
    (fresh : Fresh.laneWidth f (shape f.blocks f.degree (2*f.cap) colors)≤u)
    (size : 2*totalBits f+1≤u) :
    let s:=shape f.blocks f.degree (2*f.cap) colors
    Phase.recordWidth k board (2*f.cap)≤u ∧
    2^k+(k+3)≤u ∧ DescentSignedCableCodec.width f.degree f.cap≤u ∧
    Gather.matchUnit s f.short f.blocks f.degree (2*f.cap)≤u ∧ SixBirths.unit s≤u := by
  let r:=f.blocks
  let s:=shape r f.degree (2*f.cap) colors
  have hrow : r=2^k:=rows
  have live : 0<r:=by rw [hrow];exact Nat.two_pow_pos _
  have small : k≤r:=(Nat.lt_two_pow_self (n:=k)).le.trans_eq hrow.symm
  have boardSmall : board≤r:=boardFit.trans_eq hrow.symm
  have input:=shape_inputs_fit (D:=f.degree) (profile:=colors) live cap
  change s.inputBits≤ s.outputBits at input
  have oneDigit : 0<s.digit := by
    change 0< max colors (Nat.clog 2 (2+_+_+_+_))
    exact (Nat.clog_pos (by decide : 1<2) (by omega)).trans_le (le_max_right ..)
  have rb : r≤fields r f.degree (2*f.cap) :=Nat.le_add_right ..
  have raw : 1+f.short*fields r f.degree (2*f.cap)≤totalBits f := by
    dsimp only [r, totalBits, rawBits, Owners.inputBits]
    omega
  have cable : DescentSignedCableCodec.width f.degree f.cap≤totalBits f := by
    have scaled:=Nat.le_mul_of_pos_right (DescentSignedCableCodec.width f.degree f.cap)
      (Nat.mul_pos live (by omega : 0<2*f.cap))
    change _≤((rawBits f+DescentSignedCableCodec.width f.degree f.cap*(r*(2*f.cap)))+_)+_
    omega
  have out : s.outputBits≤Fresh.laneWidth f s := by unfold Fresh.laneWidth;omega
  have p₂ : r*(r*(2*f.cap))≤ s.pairs := by
    change r*(r*(2*f.cap))≤r*((r*binCount r f.degree)*(2*f.cap))
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by dsimp [binCount];omega)))
  have rr : r*r≤ s.pairs := (Nat.mul_le_mul_left r (Nat.le_mul_of_pos_right r (by omega))).trans p₂
  have rc : r*(2*f.cap)≤ s.pairs := (Nat.le_mul_of_pos_left _ live).trans p₂
  have outBig : s.pairs*12≤ s.outputBits := by
    change _≤ s.digit*(1+s.pairs*12)
    exact (Nat.le_add_left ..).trans (Nat.le_mul_of_pos_left _ oneDigit)
  have rBound : r≤r*r := Nat.le_mul_of_pos_right r live
  have kRows := Nat.mul_le_mul_right r small
  have bRows := Nat.mul_le_mul_right r boardSmall
  have rawDigit := Nat.mul_le_mul digit rb
  have shortRoom := Nat.le_mul_of_pos_right f.short (live.trans_le rb)
  have phase : Phase.recordWidth k board (2*f.cap)≤u := by
    unfold Phase.recordWidth Phase.unit
    rw [←hrow]
    apply max_le <;> nlinarith only [live,rBound,rr,rc,kRows,bRows,small,outBig,out,fresh]
  dsimp only
  refine ⟨phase,?_,by omega,?_,?_⟩
  · rw [←hrow]
    nlinarith only [live,digit,rawDigit,raw,size,rBound,small,shortRoom,Nat.zero_le (k*r)]
  · change max (f.short*fields r f.degree (2*f.cap)+f.short) (ProfileTable.envelope s)≤u
    apply max_le
    · omega
    · unfold ProfileTable.envelope Shape.bits
      rw [max_eq_right input]
      change s.outputBits+3*(s.digit*s.pairs)≤u
      unfold Fresh.laneWidth at fresh
      nlinarith only [fresh,Nat.zero_le (rawBits f),Nat.zero_le (s.digit*s.pairs),Nat.zero_le s.pairs]
  · change max (s.digit*s.pairs+s.outputBits) ((s.digit+1)*(s.pairs*6))≤u
    unfold Fresh.laneWidth at fresh
    apply max_le <;> nlinarith only [fresh,Nat.zero_le (rawBits f),Nat.zero_le (s.digit*s.pairs),Nat.zero_le s.pairs,
      Nat.zero_le s.outputBits]

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
