import Mathlib.Data.Nat.Log
import OAI.Hierarchy.TaggedDyadicBanks

namespace OAI
/-! # Scaling the genuine binary sorts of a repeated finite packet -/

namespace Hierarchy.Probe.PacketScale

def digits (r : ℕ) := Nat.log 2 (r+1)+2
def volume (r : ℕ) := (r+1)*(digits r)^3

theorem product_digits (r d : ℕ) : digits (r*d)≤ (d+2)*digits r := by
  let a:=Nat.log 2 (r+1)+1
  have left : r+1≤ 2^a:=(Nat.lt_pow_succ_log_self (by decide : 1<2) (r+1)).le
  have right : d+1≤ 2^d:=Nat.lt_two_pow_self
  have small : r*d+1≤ 2^(a+d):=by
    rw [pow_add]
    exact (show r*d+1≤ (r+1)*(d+1) by nlinarith).trans (Nat.mul_le_mul left right)
  have bound : Nat.log 2 (r*d+1)≤ a+d:=by
    simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) small
  have pos : 1≤ digits r:=by unfold digits; omega
  have extra : d+1≤ (d+1)*digits r:=Nat.le_mul_of_pos_right _ pos
  dsimp [a] at bound
  unfold digits at *
  nlinarith only [bound,extra]

/-- A purchased width ceiling translates the actual copy count to the
width and digit count of the public parent invoice. -/
theorem funded_volume {r w K : ℕ} (paid : r≤ K*w) :
    volume r≤ ((K+1)*(w+1))*(Nat.log 2 (K*w+1)+2)^3 := by
  have lengths : r+1≤ (K+1)*(w+1):=by nlinarith
  have digit : digits r≤ Nat.log 2 (K*w+1)+2:=
    Nat.add_le_add_right (Nat.log_mono_right (b:=2) (Nat.succ_le_succ paid)) 2
  exact Nat.mul_le_mul lengths (Nat.pow_le_pow_left digit 3)

theorem scaled_bill (r d flat counter histogram data : ℕ) :
    flat*r+counter*((r+1)*Nat.clog 2 (r+1))+histogram*volume r+
        data*((r*d+1)*(digits (r*d))^3)≤
      (flat+counter+histogram+data*((d+1)*(d+2)^3))*volume r := by
  let L:=digits r
  have pos : 1≤ L:=by dsimp [L,digits];omega
  have cubepos : 1≤ L^3:=one_le_pow₀ pos
  have raw : r≤ volume r:=(Nat.le_succ r).trans (Nat.le_mul_of_pos_right _ cubepos)
  have clog : Nat.clog 2 (r+1)≤ L:=by
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    exact (Nat.lt_pow_succ_log_self (by decide : 1<2) (r+1)).le.trans
      (Nat.pow_le_pow_right (by decide) (by dsimp [L,digits];omega))
  have one : L≤ L^3:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (n:=L) pos (by decide : 1≤3)
  have counterCap : (r+1)*Nat.clog 2 (r+1)≤ volume r:=Nat.mul_le_mul_left _ (clog.trans one)
  have dataCap : (r*d+1)*(digits (r*d))^3≤ ((d+1)*(d+2)^3)*volume r := calc
    _ ≤ ((r+1)*(d+1))*(((d+2)*digits r)^3) :=
      Nat.mul_le_mul (by nlinarith) (Nat.pow_le_pow_left (product_digits r d) 3)
    _ = _ := by unfold volume;ring
  have a:=Nat.mul_le_mul_left flat raw
  have b:=Nat.mul_le_mul_left counter counterCap
  have c:=Nat.mul_le_mul_left data dataCap
  calc
    _ ≤ flat*volume r + counter*volume r + histogram*volume r +
        data*(((d+1)*(d+2)^3)*volume r) :=
      Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add a b) (histogram*volume r)) c
    _ = _ := by ring

end Hierarchy.Probe.PacketScale

end OAI
