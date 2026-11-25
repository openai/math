import OAI.Hierarchy.DescentPackedWalshPrice
import OAI.Hierarchy.DescentPackedWalshNumerator

namespace OAI
/-! # Bit cost of the complete pair of transforms and their shared initialized tables -/
namespace Hierarchy.DescentPackedWalsh
variable {h b W C : ℕ}

theorem page_le (H u : ℕ) : page H u≤2*(H*2^u+1) := by
  unfold page rowBits
  rw [pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))

theorem numerator_price (H m : ℕ) (hb : 0<b) (small : 8*b≤h) (hw : W≤C*h) :
    let l:=laneBits m h b
    numeratorTicks H (m-l) l*W ≤
      C*((8*m+12)*h+(180*m+28)*(H*h+16*H*2^m*b)) := by
  let l:=laneBits m h b
  have fits : l≤ m:=Nat.min_le_left ..
  apply DescentPackedPayloadBudget.clock hw
  have sites:=per_layer (m:=m) H hb small
  change (H*2^(m-l))*h≤_ at sites
  change (duration H (m-l) (m-l+l)+(4+28*(H*2^(m-l)))+duration H (m-l) (m-l+l))*h≤_
  rw [Nat.sub_add_cancel fits]
  unfold duration
  nlinarith only [Nat.mul_le_mul_left (180*m+28) sites]

theorem header_price (H m : ℕ) (hb : 0<b) (small : 8*b≤h) (hw : W≤C*h) :
    let l:=laneBits m h b
    (m*span H (m-l) l b+2^(smallKey l b))*W ≤
      C*(6*m*(H*h+16*H*2^m*b+h)+(2*m+1)*2^(h/2)*h) := by
  let l:=laneBits m h b
  have spanBound := keys_fit (m:=m) hb small
  have bits : smallKey l b≤bigKey l b :=
    (Nat.mul_le_mul_right (2^l) (Nat.le_add_right b b)).trans (Nat.le_add_left _ 1)
  have sm : 2^(smallKey l b)≤2^(h/2):=Nat.pow_le_pow_right (by decide) (bits.trans spanBound)
  have bg : 2^(bigKey l b)≤2^(h/2):=Nat.pow_le_pow_right (by decide) spanBound
  have pages:=Nat.mul_le_mul_right h (page_le H (m-l))
  have sites:=per_layer (m:=m) H hb small
  change (H*2^(m-l))*h≤_ at sites
  apply DescentPackedPayloadBudget.clock hw
  change (m*(3*page H (m-l)+2^(smallKey l b)+2^(bigKey l b))+2^(smallKey l b))*h≤_
  nlinarith only [Nat.mul_le_mul_left (3*m) pages,Nat.mul_le_mul_left (6*m) sites,
    Nat.mul_le_mul_left (m+1) (Nat.mul_le_mul_right h sm),
    Nat.mul_le_mul_left m (Nat.mul_le_mul_right h bg)]

end Hierarchy.DescentPackedWalsh

end OAI
