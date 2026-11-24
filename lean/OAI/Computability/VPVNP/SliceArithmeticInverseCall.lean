import OAI.Computability.VPVNP.SliceArithmeticPowerMachine
import OAI.Computability.VPVNP.SliceArithmeticInverseInit

/-!
# A fixed bit-stack routine for inversion in the advised field

The saved exponent is the binary expansion of `p^e-2`, independent of the
coordinate query. Zero starts with a zero accumulator, while a nonzero input
starts with one. The same powering loop then handles every field size,
including the empty exponent when the field has two elements.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.InverseCall

open RAMTape
open SliceArithmeticRound (packed)

/-- Initialize the base and accumulator from the packed input, then run binary powering with
the saved inverse exponent. -/
def machine : FiniteRoutine Port := initializeInput.followedBy powerMachine

/-- Bound on inversion steps for degree `e`, limb width `w`, and `z` stored exponent bits,
including initialization. -/
def wordCap (e w z : ℕ) : ℕ := (5*z+11*(e*w)+9) + (z*(bitCap e w+1)+1)

/-- The canonical Fermat exponent fits in the total working width of the limbs. -/
def callCap (e w : ℕ) := wordCap e w (e*w)

theorem machine_word_runs {p e w : ℕ} [Fact p.Prime] (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c x : Vector p e) (bits : List Bool) (hv : TapeWord.value bits.reverse = p^e-2) :
    let cb := packed w (List.ofFn c)
    let xb := packed w (List.ofFn x)
    ∃ t ≤ wordCap e w bits.length, machine.Runs t
      (frame p e w cb xb bits [] [] [])
      (frame p e w cb xb bits [] (packed w (List.ofFn (inverse c x))) []) := by
  intro cb xb
  obtain ⟨a, ha, init⟩ := initialize_runs he hw c x bits
  by_cases hz : x = zero p e
  · subst x
    obtain ⟨b, hb, power⟩ := power_zero_runs he hw c bits bits
    rw [ite_eq_left rfl] at init
    simp only [inverse]
    exact ⟨_, by unfold wordCap; omega, init.followedBy power⟩
  · obtain ⟨b, hb, power⟩ := power_word_runs he hw c x bits bits
    rw [hv] at power
    rw [ite_eq_right hz] at init
    simp only [inverse, ite_eq_right hz]
    exact ⟨_, by unfold wordCap; omega, init.followedBy power⟩

private theorem bits_value (n : ℕ) : TapeWord.value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h, TapeWord.value, ih]
    cases b <;> simp [Nat.bit]
    omega

/-- The input base and exponent advice are retained and the inversion result
is available in the multiplier's accumulator. -/
theorem machine_runs {p e w : ℕ} [Fact p.Prime] (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c x : Vector p e) :
    let cb := packed w (List.ofFn c)
    let xb := packed w (List.ofFn x)
    let bits := (p^e-2).bits.reverse
    ∃ t ≤ callCap e w, machine.Runs t
      (frame p e w cb xb bits [] [] [])
      (frame p e w cb xb bits [] (packed w (List.ofFn (inverse c x))) []) := by
  intro cb xb bits
  have hv : TapeWord.value bits.reverse = p^e-2 := by simp [bits, bits_value]
  obtain ⟨n, hn, run⟩ := machine_word_runs he hw c x bits hv
  refine ⟨n, hn.trans ?_, run⟩
  have hlen : bits.length ≤ e*w := by
    rw [show bits.length = (p^e-2).size by simp [bits, Nat.size_eq_bits_len]]
    apply Nat.size_le.mpr
    calc
      p ^ e - 2 < p ^ e := by have := Nat.pow_pos (Fact.out : p.Prime).pos (n := e); omega
      _ ≤ (2 ^ w) ^ e := Nat.pow_le_pow_left (Word.modulus_lt hw).le _
      _ = 2 ^ (e*w) := by rw [← pow_mul, Nat.mul_comm]
  unfold callCap wordCap
  exact Nat.add_le_add (by omega) (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) _)

/-- A polynomial clock uniform in both input dimensions. -/
theorem callCap_le (e w : ℕ) : callCap e w ≤ 5000*(e+1)^3*(w+1)^3 := by
  have h := MultiplyCall.callCap_le e w
  unfold callCap wordCap bitCap
  calc
    _ ≤ (5*(e*w)+11*(e*w)+9) + ((e*w)*(2*(5*(e*w)+2+2000*(e+1)^2*(w+1)^2)+1)+1) := by gcongr
    _ ≤ _ := by ring_nf; omega

end SliceArithmetic.InverseCall

end VPVNP
end Computability
end OAI
