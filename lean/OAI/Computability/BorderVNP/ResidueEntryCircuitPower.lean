import OAI.Computability.BorderVNP.ModelGateExtension
import OAI.Computability.VPVNP.CircuitSize
import Mathlib.Data.Nat.Size

/-! # Shared arithmetic gates for powers with an input exponent

The exponent in a residue entry varies with the two pin indices. Its bits are
input operands. Horner's rule in base two squares the preceding result and
uses the current bit to select multiplication by the original base.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueFourier

open VPVNP Homogenize MvPolynomial

/-- Binary powering on little-endian ring-valued bit inputs. -/
def binaryPower {R : Type*} [Ring R] (x : R) : (w : ℕ) → (Fin w → R) → R
  | 0, _ => 1
  | w+1, b => (binaryPower x w (b ∘ Fin.succ)) ^ 2 * (1 + b 0 * (x - 1))

/-- Evaluating the powering polynomial at the bits of an integer gives the specified power. -/
theorem binaryPower_testBit {R : Type*} [Ring R] (x : R) (w n : ℕ) (hn : n < 2 ^ w) :
    binaryPower x w (fun j => if n.testBit j.val then 1 else 0) = x ^ n := by
  induction w generalizing n with
  | zero =>
    have h : n = 0 := by simpa using hn
    simp [binaryPower, h]
  | succ w ih =>
    let m := n >>> 1
    have hm : m < 2^w := by
      rw [pow_succ] at hn
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hn
    have hbits : (fun (j : Fin (w+1)) => if n.testBit j.val then (1:R) else 0) ∘ Fin.succ =
        fun j => if m.testBit j.val then 1 else 0 := by
      funext j
      simp [m, Nat.testBit_shiftRight, Nat.add_comm]
    have h := n.bit_testBit_zero_shiftRight_one
    change Nat.bit (n.testBit 0) m = n at h
    rw [binaryPower, hbits, ih _ hm, ← pow_mul]
    cases hb : n.testBit 0 <;> simp [hb, Nat.bit, Nat.mul_comm] at h ⊢
    · rw [h]
    · rw [← pow_succ, h]

/-- Binary powering commutes with evaluating all input wires. -/
theorem map_binaryPower {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (x : R) (w : ℕ) (b : Fin w → R) :
    φ (binaryPower x w b) = binaryPower (φ x) w (φ ∘ b) := by
  induction w with
  | zero => simp [binaryPower]
  | succ w ih => simp [binaryPower, ih, Function.comp_assoc]

variable {R σ : Type*} [CommRing R]

/-- The shared binary powering circuit needs five additional gates per exponent bit,
regardless of the cost of the original base and bit operands. -/
theorem binaryPower_wires {n : ℕ} (p : Program R σ n) (x : MvPolynomial σ R)
    (hx : HasWire p x) (w : ℕ) (b : Fin w → MvPolynomial σ R) (hb : ∀ i, HasWire p (b i)) :
    ∃ q : Program R σ (n+5*w), Preserves p q ∧ HasWire q (binaryPower x w b) := by
  induction w with
  | zero =>
    exact ⟨p, fun _ h => h, by simpa [binaryPower] using hasWire_const p 1⟩
  | succ w ih =>
    obtain ⟨q, hpq, hacc⟩ := ih (b ∘ Fin.succ) (fun i => hb _)
    obtain ⟨q₁, h₁, hs⟩ := append_binary q .mul hacc hacc
    obtain ⟨q₂, h₂, hd⟩ := append_binary q₁ .sub (h₁ _ (hpq _ hx)) (hasWire_const q₁ 1)
    obtain ⟨q₃, h₃, hm⟩ := append_binary q₂ .mul (h₂ _ (h₁ _ (hpq _ (hb 0)))) hd
    obtain ⟨q₄, h₄, ht⟩ := append_binary q₃ .add (hasWire_const q₃ 1) hm
    obtain ⟨q₅, h₅, hr⟩ := append_binary q₄ .mul (h₄ _ (h₃ _ (h₂ _ hs))) ht
    rw [Nat.mul_succ, ← Nat.add_assoc]
    exact ⟨q₅, fun f hf => h₅ f (h₄ f (h₃ f (h₂ f (h₁ f (hpq f hf))))),
      by simpa [binaryPower, BinOp.apply, pow_two] using hr⟩

/-- A fixed exponent uses the bit constants in the same bounded circuit. -/
theorem circuitSize_power_le (x : MvPolynomial σ R) (n : ℕ) :
    circuitSize (x ^ n) ≤ circuitSize x + 5*n.size := by
  obtain ⟨c, hc⟩ := circuitSize_spec x
  have hx : HasWire c.program x := ⟨c.output, hc⟩
  let b (j : Fin n.size) : MvPolynomial σ R := if n.testBit j.val then 1 else 0
  obtain ⟨q, _, v, hv⟩ := binaryPower_wires c.program x hx n.size b (by
    intro i
    dsimp [b]
    split
    · simpa only [map_one] using hasWire_const c.program (1 : R)
    · simpa only [map_zero] using hasWire_const c.program (0 : R))
  refine circuitSize_le_iff.mpr ⟨_, le_rfl, ⟨q,v⟩, hv.trans ?_⟩
  exact binaryPower_testBit x n.size n (Nat.lt_size_self n)

end ResidueFourier

end BorderVNP
end Computability
end OAI
