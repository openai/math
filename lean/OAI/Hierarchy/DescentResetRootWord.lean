import OAI.Hierarchy.DescentResetMiddleCalendar

namespace OAI
/-! # The maximum physical result width of the four reset root instructions -/

namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentPackedPrivateMenu DescentFallbackPeriod.Projected

noncomputable section
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h)

def rootWord (k Ht f cap C packet instruction batches : ℕ) :=
  let L := 2^k
  let layers := DescentRecordedRotorLayers.width f cap
  let slots := max (Fintype.card (DescentCommonPalette.rotor board).Edge) (2^(Ht+1))
  let geometry (bits : ℕ) := fieldBits board k Ht (L*(2*cap)) bits C packet*(slots*5)
  max (max (DescentRotorWindowArchive.output n L cap) (instruction*batches))
    (max (geometry 0) (geometry layers))

private theorem bits_le (a : ℕ) : ProtocolRAMPurchaseSampler.bits a ≤ a+2 :=
  Nat.add_le_add_right (Nat.log_le_self 2 (a+1)) 1

/-- Public polynomial bound in the old grain capacity and number of low cells.
The two cardinal factors are the immutable rotor and fallback template sizes. -/
theorem rootWord_poly (k Ht f cap C packet instruction batches : ℕ) :
    let Y := 2^n
    let N := 2^k*(2*cap)
    let slots := max (Fintype.card (DescentCommonPalette.rotor board).Edge) (2^(Ht+1))
    let roster := (2*((Y+1)+((2*h+4)*Y+(Y+1)*2^(Ht+1))))*2^(k+1)
    let units := max (C*packet) ((2+2*h*C)*packet)
    rootWord board k Ht f cap C packet instruction batches ≤
      (N+2)*(Y*Y) + instruction*batches +
      (N+3+roster+2*(21*2^f*(cap+1)+1)*units)*(slots*5) := by
  dsimp only
  let N := 2^k*(2*cap)
  let L := DescentRecordedRotorLayers.width f cap
  let U := max (C*packet) ((2+2*h*C)*packet)
  let A := 2*(21*2^f*(cap+1)+1)
  let R := (2*((2^n+1)+((2*h+4)*2^n+(2^n+1)*2^(Ht+1))))*2^(k+1)
  have mass : 2^L ≤ A := ProtocolRAMPurchaseSampler.span_le _
  have small : 2^0 ≤ A := (Nat.one_le_two_pow).trans mass
  have chart : (DescentDenseHostOrder.roster board k Ht).card ≤ R :=
    DescentDenseHostOrder.roster_bound board k Ht
  have digits (l : ℕ) (paid : 2^l ≤ A) :
      fieldBits board k Ht N l C packet ≤ N+3+R+A*U := by
    apply (bits_le _).trans
    have products := Nat.mul_le_mul_right U paid
    change max N (max 1 (max _ (2^l*U)))+2 ≤ _
    omega
  have matrix := Nat.mul_le_mul_right ((2^n)*(2^n)) (bits_le N)
  let slots := max (Fintype.card (DescentCommonPalette.rotor board).Edge) (2^(Ht+1))
  have f₀ := Nat.mul_le_mul_right (slots*5) (digits 0 small)
  have f₁ := Nat.mul_le_mul_right (slots*5) (digits L mass)
  change max (max (ProtocolRAMPurchaseSampler.bits N*((2^n)*(2^n))) (instruction*batches))
    (max (fieldBits board k Ht N 0 C packet*(slots*5))
      (fieldBits board k Ht N L C packet*(slots*5))) ≤
    (N+2)*((2^n)*(2^n))+instruction*batches+(N+3+R+A*U)*(slots*5)
  omega

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
