import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI
/-! # Dyadic rounding and the size coefficient of a histogram row -/

namespace ThreeFlat.Diagonal.HistogramTileNetwork

def siteHeight (r d : ℕ) := Nat.clog 2 (max r (r*d))

theorem siteHeight_room (r d : ℕ) : max r (r*d) ≤ 2^siteHeight r d :=
  Nat.le_pow_clog (by decide) _

theorem siteHeight_capacity (r d : ℕ) : 2^siteHeight r d ≤ (r+1)*(2*(d+1)) := by
  have hm : max r (r*d) ≤ (r+1)*(d+1) := by
    apply max_le <;> simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] <;> omega
  cases ht : siteHeight r d with
  | zero =>
    exact Nat.mul_pos (Nat.succ_pos r) (Nat.mul_pos (by decide) (Nat.succ_pos d))
  | succ t =>
    have hl : t < Nat.clog 2 (max r (r*d)) := by change t < siteHeight r d; omega
    have hp := Nat.pow_lt_of_lt_clog hl
    rw [pow_succ]
    rw [show (r+1)*(2*(d+1)) = ((r+1)*(d+1))*2 by ring]
    omega

/-- The coefficient depends only on the two truth table widths and the fixed motif. -/
def partyCoefficient (b k h e d : ℕ) :=
  2^(e*k+h)*(e*k+h+2) + h + 2^(b+(e*d+e*d))*(b+(e*d+e*d)+2) + 2*(e*d) +
    (2*(h+e))*(64000*(d+1))

theorem absorb_party_charge (r d h e A B : ℕ) :
    let m := siteHeight r d
    let c := 2^m*(32000*(m+1)^3)
    r*A + r*h + 2*(h*c) + (r*B + 2*(e*(r*d)) + 2*(e*c)) ≤
      (r+1)*(A+h+B+2*(e*d)+(2*(h+e))*(64000*(d+1)))*(m+1)^3 := by
  dsimp only
  let t := (r+1)*(siteHeight r d+1)^3
  have ht : r ≤ t :=
    (Nat.le_succ r).trans (Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) _))
  have hc : 2^siteHeight r d*(32000*(siteHeight r d+1)^3) ≤ t*(64000*(d+1)) := by
    calc
      _ ≤ ((r+1)*(2*(d+1)))*(32000*(siteHeight r d+1)^3) :=
        Nat.mul_le_mul_right _ (siteHeight_capacity r d)
      _ = _ := by dsimp [t]; ring
  calc
    _ = r*(A+h+B+2*(e*d)) + (2*(h+e))*(2^siteHeight r d*(32000*(siteHeight r d+1)^3)) := by ring
    _ ≤ t*(A+h+B+2*(e*d)) + (2*(h+e))*(t*(64000*(d+1))) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ ht) (Nat.mul_le_mul_left _ hc)
    _ = _ := by dsimp [t]; ring

end ThreeFlat.Diagonal.HistogramTileNetwork

end OAI
