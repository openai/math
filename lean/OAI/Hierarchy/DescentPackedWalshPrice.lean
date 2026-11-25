import OAI.Hierarchy.DescentPackedWalshLanes
import OAI.Hierarchy.DescentPackedWalshPasses
import OAI.Hierarchy.DescentPackedPayloadBudget

namespace OAI
/-! # One load vector costs a linear number of packed digit bits per Walsh layer -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup

theorem keys_fit {m h b : ℕ} (hb : 0<b) (small : 8*b≤h) :
    bigKey (laneBits m h b) b≤h/2 := by
  have pos : 0<h/(8*b):=Nat.div_pos small (by omega)
  have bare:=Nat.pow_log_le_self 2 pos.ne'
  have lanes : 2^(laneBits m h b)≤h/(8*b) :=
    (Nat.pow_le_pow_right (by decide) (Nat.min_le_right ..)).trans bare
  have room:=(Nat.le_div_iff_mul_le (show 0<8*b by omega)).mp lanes
  unfold bigKey
  apply (Nat.le_div_iff_mul_le (by decide)).2
  have coeff : 1≤b*2^laneBits m h b:=Nat.mul_pos hb (Nat.two_pow_pos _)
  nlinarith only [room,coeff]

theorem per_layer {m h b : ℕ} (H : ℕ) (hb : 0<b) (_small : 8*b≤h) :
    let l:=laneBits m h b
    (H*2^(m-l))*h≤H*h+16*H*2^m*b := by
  let l:=laneBits m h b
  have below : l≤ m:=Nat.min_le_left _ _
  by_cases all : l=m
  · change H*2^(m-l)*h≤H*h+16*H*2^m*b
    rw [all,Nat.sub_self,pow_zero,Nat.mul_one]
    exact Nat.le_add_right _ _
  · have last : l=Nat.log 2 (h/(8*b)):=by dsimp [l,laneBits] at *;omega
    have raw:=Nat.lt_pow_succ_log_self (by decide : 1<2) (h/(8*b))
    rw [←last,pow_succ] at raw
    have rate : h<(2^l*2)*(8*b):=(Nat.div_lt_iff_lt_mul (by omega)).mp raw
    have lift:=Nat.mul_le_mul_left (H*2^(m-l)) rate.le
    have product : 2^(m-l)*2^l=2^m := by rw [←pow_add,Nat.sub_add_cancel below]
    calc
      _ ≤ H*2^(m-l)*((2^l*2)*(8*b)) := lift
      _ = 16*H*(2^(m-l)*2^l)*b := by ring
      _ ≤ _ := by rw [product];omega

theorem transform_price {m h b W C : ℕ} (H : ℕ) (hb : 0<b) (small : 8*b≤h) (hw : W≤C*h) :
    duration H (m-laneBits m h b) m*W ≤ C*((4*m+4)*h+90*m*(H*h+16*H*2^m*b)) := by
  apply DescentPackedPayloadBudget.clock hw
  have sites:=per_layer H hb small (m:=m)
  dsimp at sites
  unfold duration
  nlinarith only [Nat.mul_le_mul_left (90*m) sites]

end Hierarchy.DescentPackedWalsh

end OAI
