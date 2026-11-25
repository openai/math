import OAI.Computability.NearSquareRoot.PrecisionFlatWalshBits

/-! # The Walsh matrix on a contiguous address window

Selecting the bits from `d` through `d+L-1` leaves the high quotient and
the low remainder fixed. On each such fiber the matrix entry is the
ordinary Walsh entry on the intervening `L` bits.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshWindow

open Finset

/-- Place an address bit in a contiguous window starting at offset `d`. -/
def embed (n L d : ℕ) (h : d + L ≤ n) : Fin L ↪ Fin n where
  toFun j := ⟨j.val + d, by omega⟩
  inj' := by
    intro i j hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)

/-- The selected physical address bits of the window. -/
def bits (n L d : ℕ) (h : d + L ≤ n) : Finset (Fin n) :=
  univ.image (embed n L d h)

theorem mem_bits {n L d : ℕ} (h : d + L ≤ n) (p : Fin n) :
    p ∈ bits n L d h ↔ d ≤ p.val ∧ p.val < d + L := by
  constructor
  · intro hp
    obtain ⟨q, _, rfl⟩ := mem_image.mp hp
    change d ≤ q.val + d ∧ q.val + d < d + L
    omega
  · rintro ⟨hlo, hhi⟩
    refine mem_image.mpr ⟨⟨p.val - d, by omega⟩, mem_univ _, Fin.ext ?_⟩
    exact Nat.sub_add_cancel hlo

/-- A window retains exactly the selected address bits. -/
def middle {n : ℕ} (L d : ℕ) (x : Fin (2^n)) : Fin (2^L) :=
  ⟨x.val / 2^d % 2^L, Nat.mod_lt _ (by positivity)⟩

theorem middle_testBit {n L d : ℕ} (h : d + L ≤ n) (x : Fin (2^n)) (q : Fin L) :
    (middle L d x).val.testBit q.val = x.val.testBit (embed n L d h q).val := by
  simp only [middle, Nat.testBit_mod_two_pow, decide_eq_true q.isLt, Bool.true_and,
    Nat.testBit_div_two_pow]
  rfl

theorem offBits_window {n L d : ℕ} (h : d + L ≤ n) (x y : Fin (2^n)) :
    BoxFin.offBits (bits n L d h) x y ↔
      x.val / 2^(d+L) = y.val / 2^(d+L) ∧ x.val % 2^d = y.val % 2^d := by
  constructor
  · intro he
    constructor
    · apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
      by_cases hi : i + (d+L) < n
      · exact he ⟨_, hi⟩ (by rw [mem_bits]; change ¬ (d ≤ i+(d+L) ∧ i+(d+L) < d+L); omega)
      · have hp : 2^n ≤ 2^(i+(d+L)) := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hp), Nat.testBit_eq_false_of_lt (y.isLt.trans_le hp)]
    · apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < d
      · simp only [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
        exact he ⟨i, by omega⟩ (by rw [mem_bits]; change ¬ (d ≤ i ∧ i < d+L); omega)
      · simp [Nat.testBit_mod_two_pow, hi]
  · rintro ⟨hh, hl⟩ p hp
    rw [mem_bits] at hp
    by_cases hlo : p.val < d
    · simpa only [Nat.testBit_mod_two_pow, decide_eq_true hlo, Bool.true_and] using
        congrArg (fun t : ℕ => t.testBit p.val) hl
    · have hhi : d+L ≤ p.val := by omega
      simpa only [Nat.testBit_div_two_pow, Nat.sub_add_cancel hhi] using
        congrArg (fun t : ℕ => t.testBit (p.val - (d+L))) hh

theorem overlap_window {n L d : ℕ} (h : d + L ≤ n) (x y : Fin (2^n)) :
    BoxFin.physicalOverlap (bits n L d h) x y =
      BoxFin.physicalOverlap univ (middle L d x) (middle L d y) := by
  unfold BoxFin.physicalOverlap bits
  rw [filter_image, card_image_of_injective _ (embed n L d h).injective]
  congr 1
  apply filter_congr
  intro i _
  rw [middle_testBit h, middle_testBit h]

/-- Extracting the active field identifies every nonzero entry with its
full Walsh matrix entry. This also covers empty and full-width windows. -/
theorem flatWalsh_window (n L d : ℕ) (h : d + L ≤ n) (x y : Fin (2^n)) :
    BoxFin.flatWalsh (bits n L d h) x y =
      if x.val / 2^(d+L) = y.val / 2^(d+L) ∧ x.val % 2^d = y.val % 2^d then
        BoxFin.flatWalsh univ (middle L d x) (middle L d y) else 0 := by
  classical
  have hu : BoxFin.offBits univ (middle L d x) (middle L d y) := fun p hp => (hp (mem_univ p)).elim
  simp only [BoxFin.flatWalsh, Matrix.of_apply, offBits_window, overlap_window, hu, ite_true]
  rw [bits, card_image_of_injective _ (embed n L d h).injective]

end FlatWalshWindow

end NearSquareRoot
end Computability
end OAI
