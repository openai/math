import OAI.Computability.NearSquareRoot.PhysicalWalshNodeXorBits

/-! # Exchanging two complete bit fields of a binary ordinal -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SwapWord

/-- Source position of a bit after exchanging the nonoverlapping windows. -/
def pos (lo hi w i : ℕ) := if lo ≤ i ∧ i < lo+w then i-lo+hi else
  if hi ≤ i ∧ i < hi+w then i-hi+lo else i

/-- The width-`w` binary field above position `p`. -/
def field (p w n : ℕ) := n/2^p%2^w

private def join (w p b : ℕ) := p*2^w+b

/-- Concatenating the same five pieces in their new positions needs no
power-of-two assumption on the leading row count. -/
def run (lo hi w n : ℕ) :=
  join lo (join w (join (hi-(lo+w)) (join w (n/2^(hi+w)) (field lo w n))
    (field (lo+w) (hi-(lo+w)) n)) (field hi w n)) (n%2^lo)

private theorem join_bit (w p b i : ℕ) (h : b<2^w) :
    (join w p b).testBit i = if i<w then b.testBit i else p.testBit (i-w) := by
  unfold join; rw [Nat.mul_comm,Nat.testBit_two_pow_mul_add _ h]

private theorem field_lt (p w n : ℕ) : field p w n < 2^w := Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem field_bit (p w n i : ℕ) (h : i < w) : (field p w n).testBit i = n.testBit (i+p) := by
  simp [field,Nat.testBit_div_two_pow,h]

/-- Little-endian source ordinal for every bit of the five-field reassembly. -/
theorem run_bit (lo hi w n : ℕ) (apart : lo+w ≤ hi) (i : ℕ) :
    (run lo hi w n).testBit i = n.testBit (pos lo hi w i) := by
  unfold run
  rw [join_bit _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases low : i<lo
  · simp [low,pos,show ¬lo ≤ i by omega,show ¬hi ≤ i by omega]
  rw [ite_eq_right low, join_bit _ _ _ _ (field_lt ..)]
  by_cases bottom : i-lo < w
  · rw [ite_eq_left bottom,field_bit _ _ _ _ bottom]
    simp [pos,show lo ≤ i ∧ i < lo+w by omega]
  rw [ite_eq_right bottom,join_bit _ _ _ _ (field_lt ..)]
  by_cases gap : i-lo-w < hi-(lo+w)
  · rw [ite_eq_left gap,field_bit _ _ _ _ gap]
    simp only [pos,show ¬(lo ≤ i ∧ i<lo+w) by omega,show ¬(hi ≤ i ∧ i<hi+w) by omega,ite_false]
    apply congrArg (Nat.testBit n); omega
  rw [ite_eq_right gap,join_bit _ _ _ _ (field_lt ..)]
  by_cases top : i-lo-w-(hi-(lo+w)) < w
  · rw [ite_eq_left top,field_bit _ _ _ _ top]
    simp only [pos,show ¬(lo ≤ i ∧ i<lo+w) by omega,show hi ≤ i ∧ i<hi+w by omega,and_self,ite_true,ite_false]
    apply congrArg (Nat.testBit n); omega
  rw [ite_eq_right top,Nat.testBit_div_two_pow]
  simp only [pos,show ¬(lo ≤ i ∧ i<lo+w) by omega,show ¬(hi ≤ i ∧ i<hi+w) by omega,ite_false]
  apply congrArg (Nat.testBit n); omega

/-- The low `g` bits can be swapped before the wide rectangular interchange.
This leaves a complete trailing payload of at least `2^g` while that
interchange handles the two remaining `w-g` bit fields. -/
theorem split (lo hi w g n : ℕ) (apart : lo+w ≤ hi) (cut : g ≤ w) :
    run lo hi g (run (lo+g) (hi+g) (w-g) n) = run lo hi w n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [run_bit _ _ _ _ (by omega),run_bit _ _ _ _ (by omega),run_bit _ _ _ _ apart]
  apply congrArg (Nat.testBit n)
  simp only [pos]
  split_ifs <;> omega

/-- Natural mixed-radix floor/mod form, with arbitrary prefix and binary
field sizes. -/
theorem run_eq (lo hi w n : ℕ) (apart : lo+w ≤ hi) :
    run lo hi w n = n/2^(hi+w)*2^(hi+w) + field lo w n *2^hi + field (lo+w) (hi-(lo+w)) n*2^(lo+w) +
      field hi w n*2^lo + n%2^lo := by
  let G := hi-(lo+w)
  have high : hi = lo+w+G := by dsimp only [G];omega
  change (((n/2^(hi+w)*2^w + field lo w n)*2^G + field (lo+w) G n)*2^w+field hi w n)*2^lo+n%2^lo = _
  generalize n/2^(hi+w) = pre, field lo w n = low, field (lo+w) G n = mid, field hi w n = highField, n%2^lo = tail
  rw [high];simp only [pow_add];ring

end PhysicalWalshNode.SwapWord

end NearSquareRoot
end Computability
end OAI
