import OAI.Computability.VPVNP.RAMSortLayers
import Mathlib.Data.Nat.Bitwise

namespace OAI
/-! # Affine row-bit controls for a uniform memory checker -/

namespace ThreeFlat.Diagonal.TraceMemoryCircuit

open Computability.VPVNP.RAMSort

variable {d w : ℕ}

/-- A bit index in a physical track's address, or the successor guard. -/
abbrev MemoryControl (d _w : ℕ) := (Fin (d+2) × Fin 2) ⊕ Unit

def controlsAt (v : Fin (2^d)) : MemoryControl d w → Bool
  | .inl (j,i) => (2*v.val+i.val).testBit j.val
  | .inr _ => decide (v.val+1 < 2^d)

theorem lt_partner_iff (g j : ℕ) : g < partner j g ↔ g.testBit j = false := by
  have ht (t : ℕ) (h : j < t) : g.testBit t = (partner j g).testBit t := by
    simp [partner, Nat.testBit_two_pow_of_ne (Nat.ne_of_lt h)]
  cases h : g.testBit j with
  | false =>
    simp only [iff_true]
    exact Nat.lt_of_testBit j h (by simp [partner,h]) ht
  | true =>
    have hp : partner j g < g :=
      Nat.lt_of_testBit j (by simp [partner,h]) h (fun t h => (ht t h).symm)
    exact iff_of_false (Nat.not_lt_of_ge hp.le) (by decide)

theorem phase_bit (a g : ℕ) : phaseDirection a g = !(g.testBit a) := by
  unfold phaseDirection
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (g / 2^a) with h | h <;> simp [h]

/-- Exactly two affine address bits determine the min/max choice. -/
theorem polarity_eq_bits (a j g : ℕ) :
    (if g < partner j g then phaseDirection a g else !(phaseDirection a g)) =
      (g.testBit j == g.testBit a) := by
  cases hj : g.testBit j with
  | false =>
    have h := (lt_partner_iff g j).2 hj
    cases ha : g.testBit a <;> simp [h,phase_bit,ha]
  | true =>
    have h : ¬ g < partner j g := fun hp => by
      have bad := (lt_partner_iff g j).1 hp
      simp [hj] at bad
    cases ha : g.testBit a <;> simp [h,phase_bit,ha]

end ThreeFlat.Diagonal.TraceMemoryCircuit

end OAI
