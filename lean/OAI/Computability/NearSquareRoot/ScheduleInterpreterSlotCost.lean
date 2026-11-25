import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

/-!
# Time and radius of a physical trial slot

The alphabet and tape count are fixed. The raw tape widths and publication
length may grow with the input, while the two slot counters contribute only
their current offsets to the common radius.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotCost

variable (I : Type) [Fintype I]

def space (W a : ℕ) : ℕ := Fintype.card (I ⊕ Bool)*(2*(W+2*(a+3))+1)

def radius (W N i a : ℕ) : ℕ :=
  let s := space I W a
  max (3*(i+a)+5) (s+1+Fintype.card (Option (I ⊕ Bool))*(8*s+2*N+7))

def coefficient (K H : ℕ) : ℕ :=
  let B := Fintype.card (I ⊕ Bool)*(2*(K+6)+1)
  max 5 (B+1+Fintype.card (Option (I ⊕ Bool))*(8*B+2*H+7))

/-- One constant bounds the physical slot for all inputs and all counter offsets. -/
theorem radius_le {W N n i a K H : ℕ} (hW : W ≤ K*(n+1)) (hN : N ≤ H*(n+1)) :
    radius I W N i a ≤ coefficient I K H*(n+i+a+1) := by
  let L := n+i+a+1
  let B := Fintype.card (I ⊕ Bool)*(2*(K+6)+1)
  have unit : 1 ≤ L := by dsimp [L]; omega
  have n_le : n+1 ≤ L := by dsimp [L]; omega
  have clock : 2*(a+3) ≤ 6*L := by dsimp [L]; omega
  have hw := hW.trans (Nat.mul_le_mul_left K n_le)
  have hn := hN.trans (Nat.mul_le_mul_left H n_le)
  have hs : space I W a ≤ B*L := by
    dsimp [space,B]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith only [hw,clock,unit]
  have inner : 8*space I W a+2*N+7 ≤ (8*B+2*H+7)*L := by
    nlinarith only [hs,hn,unit]
  have cap := Nat.mul_le_mul_left (Fintype.card (Option (I ⊕ Bool))) inner
  apply max_le
  · apply le_trans _ (Nat.mul_le_mul_right L (le_max_left _ _))
    dsimp [L]
    omega
  · apply le_trans _ (Nat.mul_le_mul_right L (le_max_right _ _))
    change space I W a+1+_ ≤ (B+1+Fintype.card (Option (I ⊕ Bool))*(8*B+2*H+7))*L
    nlinarith only [hs,cap,unit]

/-- Charge both counter scans, both stationary handoffs, and the metered trial. -/
theorem time_le (i a : ℕ) :
    2*(i+a)+5+1+106*2^a+1+(2*(i+a)+5) ≤ 120*(2^a+i+a+1) := by omega

end Uniform.SlotCost

end NearSquareRoot
end Computability
end OAI
