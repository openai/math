import OAI.Hierarchy.DescentPackedMinimum

namespace OAI
/-! # A shared lookup uses the payload width even when absolute addresses need a larger word -/

namespace Hierarchy.DescentPackedPayloadBudget
open DescentSIMDLookup DescentPackedMinimum

theorem clock {ticks W h C bill : ℕ} (hardware : W≤C*h) (charged : ticks*h≤bill) :
    ticks*W≤C*bill := by
  calc
    _ ≤ ticks*(C*h) := Nat.mul_le_mul_left _ hardware
    _ = C*(ticks*h) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ charged

theorem arena {bytes h original : ℕ} (shelf : bytes≤2^(h/2)) (fund : 2^h≤original) :
    bytes^2≤original := by
  calc
    _ ≤ (2^(h/2))^2 := Nat.pow_le_pow_left shelf 2
    _ = 2^(2*(h/2)) := by rw [←pow_mul,Nat.mul_comm (h/2)]
    _ ≤ _ := (Nat.pow_le_pow_right (by decide) (Nat.mul_div_le h 2)).trans fund

private theorem twice_le_power (d : ℕ) : 2*d≤2^d := by
  induction d with
  | zero=>decide
  | succ d ih=>
    rw [pow_succ,Nat.mul_succ]
    by_cases base : d=0
    · subst d;decide
    · have two : 2≤2^d := Nat.one_lt_two_pow base
      omega

theorem table_bits {words W h C original : ℕ} (table : words≤2^(h/2)) (hardware : W≤C*h)
    (fund : 2^h≤original) : words*W≤C*original := by
  apply clock hardware
  have limit : h≤2^(h-h/2) := (show h≤2*(h-h/2) by omega).trans (twice_le_power _)
  calc
    _ ≤ 2^(h/2)*2^(h-h/2) := Nat.mul_le_mul table limit
    _ = 2^h := by rw [←pow_add];congr 1;omega
    _ ≤ _ := fund

theorem search_price {q H G W h C a : ℕ} (L : Layout q)
    (small : 0<a) (payload : 2*a≤h) (hardware : W≤C*h) :
    ((4+q*cost L.work (H*chunks G (lanes h a)))+DescentFirstMinimumRAM.ticks L.result L.ledger (List.range q))*W
      ≤ C*(200*(q+1)*(h+H*h+4*H*G*a)) := clock hardware (bit_price L h a H G small payload)

end Hierarchy.DescentPackedPayloadBudget

end OAI
