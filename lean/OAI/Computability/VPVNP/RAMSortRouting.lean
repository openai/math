import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic

/-!
# Routing comparator layers between sites

In Lemma 10.1 of *VP and VNP differ over every field*, every site holds a block of
`2^h = 4H` consecutive positions. A comparator at stride `2^j` pairs positions whose
indices differ in bit `j`. When `j < h` this changes only the offset inside the block.
Otherwise every record in the block goes to the same other site with its offset preserved.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

/-- The comparator partner of an array index in a layer with stride `2^j`. -/
def partner (j x : ℕ) : ℕ := x ^^^ 2 ^ j

@[simp] theorem partner_partner (j x : ℕ) : partner j (partner j x) = x :=
  Nat.xor_xor_cancel_right x (2 ^ j)

theorem partner_ne (j x : ℕ) : partner j x ≠ x := by
  intro heq
  have h := congrArg (fun y ↦ x ^^^ y) heq
  simp [partner] at h

/-- A comparator partner is a valid position in the same power-of-two array. -/
theorem partner_lt {b j x : ℕ} (hx : x < 2 ^ b) (hj : j < b) : partner j x < 2 ^ b :=
  Nat.xor_lt_two_pow hx (Nat.pow_lt_pow_right (by decide) hj)

private theorem partner_split (j site h : ℕ) {off : ℕ} (ho : off < 2 ^ h) :
    partner j (site * 2 ^ h + off) =
      (site ^^^ 2 ^ j / 2 ^ h) * 2 ^ h + (off ^^^ 2 ^ j % 2 ^ h) := by
  have hdiv : (site * 2 ^ h + off) / 2 ^ h = site := by
    rw [Nat.mul_comm site, Nat.mul_add_div (Nat.two_pow_pos h), Nat.div_eq_of_lt ho,
      Nat.add_zero]
  rw [← Nat.div_add_mod' (partner j (site * 2 ^ h + off)) (2 ^ h)]
  simp only [partner, Nat.xor_div_two_pow, Nat.xor_mod_two_pow, hdiv, Nat.mul_add_mod_of_lt ho]

/-- The low bit belongs to the offset, so every comparator is internal to its site. -/
theorem partner_local (site : ℕ) {h j off : ℕ} (ho : off < 2 ^ h) (hj : j < h) :
    partner j (site * 2 ^ h + off) = site * 2 ^ h + partner j off := by
  have hstride : 2 ^ j < 2 ^ h := Nat.pow_lt_pow_right (by decide) hj
  rw [partner_split j site h ho]
  simp [Nat.div_eq_of_lt hstride, Nat.mod_eq_of_lt hstride, partner]

/-- A high bit changes the site and leaves every within-site offset unchanged. -/
theorem partner_cross (site : ℕ) {h j off : ℕ} (ho : off < 2 ^ h) (hj : h ≤ j) :
    partner j (site * 2 ^ h + off) = partner (j - h) site * 2 ^ h + off := by
  have hm : (2 ^ j : ℕ) % 2 ^ h = 0 := Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 hj)
  rw [partner_split j site h ho]
  simp [Nat.pow_div hj (by decide : 0 < (2 : ℕ)), hm, partner]

/-- The partner of a lower-half index lies at the same offset in the upper half. -/
theorem partner_lo {j i : ℕ} (hi : i < 2 ^ j) : partner j i = i + 2 ^ j := by
  simpa [partner, Nat.add_comm] using (partner_cross 0 hi (le_refl j))

/-- The reverse comparison sends the upper-half index back to its lower-half mate. -/
theorem partner_hi {j i : ℕ} (hi : i < 2 ^ j) : partner j (i + 2 ^ j) = i := by
  rw [← partner_lo hi, partner_partner]

/-- Stride exponents in phase `a` are `a-1, …, 0`. The ones requiring a whole-block
exchange are exactly those at least `h`. -/
def crossStrides (h a : ℕ) : Finset ℕ := (Finset.range a).filter (h ≤ ·)

@[simp] theorem mem_crossStrides {h a j : ℕ} : j ∈ crossStrides h a ↔ h ≤ j ∧ j < a := by
  simp [crossStrides, and_comm]

@[simp] theorem card_crossStrides (h a : ℕ) : (crossStrides h a).card = a - h := by
  have hIco : crossStrides h a = Finset.Ico h a := Finset.ext fun _ ↦ by simp
  rw [hIco, Nat.card_Ico]

/-- Summing over the phases of a `2^(h+d)` array gives the factor in equation (10.1).
Phase zero is included in the index set and has no comparator layers. -/
theorem total_crossStrides (h d : ℕ) :
    ∑ a ∈ Finset.range (h + d + 1), (crossStrides h a).card = (d + 1).choose 2 := by
  rw [Nat.add_assoc, Finset.sum_range_add]
  have hlocal : ∑ a ∈ Finset.range h, (crossStrides h a).card = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp [Nat.sub_eq_zero_of_le (Finset.mem_range.mp ha).le]
  rw [hlocal]
  simp [Finset.sum_range_id, Nat.choose_two_right]

end RAMSort

end VPVNP
end Computability
end OAI
