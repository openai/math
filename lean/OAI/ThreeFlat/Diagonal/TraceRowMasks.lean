import OAI.Computability.VPVNP.RAMMemory
import Mathlib.Tactic

namespace OAI
/-! # Row addresses for the sorted RAM trace

Two logical slots occupy each physical row. A comparator for bit zero stays
in that row, and any higher comparator bit translates the physical row by a
single-bit mask. Adjacent physical rows differ in a nonempty low-bit prefix.
-/

namespace ThreeFlat.Diagonal.TraceRowMasks

/-- Flipping the low comparator bit exchanges the two slots of a physical row. -/
theorem low_partner_row (j : ℕ) : (j ^^^ 1) / 2 = j / 2 := by
  rw [Nat.xor_div_two]
  simp

/-- A higher comparator bit becomes the preceding bit after packing slot pairs. -/
theorem high_partner_row (j s : ℕ) :
    (j ^^^ 2 ^ (s + 1)) / 2 = (j / 2 ^^^ 2 ^ s) := by
  rw [Nat.xor_div_two, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- The carry in an adjacent-row link flips a prefix of between one and
`d` low bits. Consequently `d` public masks suffice for all such links. -/
theorem adjacent_mask {r d : ℕ} (bound : r + 1 < 2 ^ d) :
    ∃ k, 0 < k ∧ k ≤ d ∧ (r ^^^ (r + 1)) = 2 ^ k - 1 := by
  induction d generalizing r with
  | zero => simp at bound
  | succ d ih =>
    rw [pow_succ] at bound
    have last : (r ^^^ (r + 1)) % 2 = 1 := Nat.xor_mod_two_eq_one.mpr (by omega)
    have high := Nat.xor_div_two (a := r) (b := r + 1)
    by_cases even : r % 2 = 0
    · have hh : (r + 1) / 2 = r / 2 := by omega
      rw [hh, Nat.xor_self] at high
      refine ⟨1, by decide, by omega, ?_⟩
      norm_num
      omega
    · have hh : (r+1) / 2 = r / 2 + 1 := by omega
      rw [hh] at high
      obtain ⟨k, hk, hd, H⟩ := ih (r := r / 2) (by omega)
      refine ⟨k+1, by omega, by omega, ?_⟩
      rw [H] at high
      rw [pow_succ]
      have hp : 0 < 2 ^ k := by positivity
      omega

/-- A check on consecutive logical slots either lies within a physical row,
or crosses the adjacent-row carry mask. -/
theorem adjacent_slot_rows {j d : ℕ} (fits : (j + 1) / 2 < 2 ^ d) :
    j / 2 = (j + 1) / 2 ∨
      ∃ k, 0 < k ∧ k ≤ d ∧ (j / 2 ^^^ ((j+1) / 2)) = 2 ^ k - 1 := by
  by_cases same : j / 2 = (j + 1) / 2
  · exact Or.inl same
  · have next : (j + 1) / 2 = j / 2 + 1 := by omega
    rw [next] at fits ⊢
    exact Or.inr (adjacent_mask fits)

/-- Pack the pins of two external words into slots of consecutive rows,
beginning at physical row `base`. Earlier and later header words are supplied
by the background header. -/
def interleavedHeader {α : Type*} (base count : ℕ) (background x y : ℕ → α) (a : ℕ) : α :=
  if 2 * base ≤ a ∧ a < 2 * (base + count) then
    if a % 2 = 0 then x (a / 2 - base) else y (a / 2 - base)
  else background a

@[simp] theorem interleavedHeader_even {α : Type*} {base count j : ℕ} (hj : j < count)
    (background x y : ℕ → α) :
    interleavedHeader base count background x y (2*(base+j)) = x j := by
  simp [interleavedHeader, show 2*base ≤ 2*(base+j) by omega,
    show 2*(base+j) < 2*(base+count) by omega]

@[simp] theorem interleavedHeader_odd {α : Type*} {base count j : ℕ} (hj : j < count)
    (background x y : ℕ → α) :
    interleavedHeader base count background x y (2*(base+j)+1) = y j := by
  have hdiv : (2 * (base+j) + 1) / 2 = base+j := by omega
  simp [interleavedHeader, show 2*base ≤ 2*(base+j)+1 by omega,
    show 2*(base+j)+1 < 2*(base+count) by omega,
    show (2*(base+j)+1) % 2 = 1 by omega, hdiv]

theorem interleavedHeader_outside {α : Type*} {base count a : ℕ}
    (ha : a < 2 * base ∨ 2 * (base + count) ≤ a) (background x y : ℕ → α) :
    interleavedHeader base count background x y a = background a := by
  simp [interleavedHeader, show ¬ (2 * base ≤ a ∧ a < 2 * (base + count)) by omega]

open Computability.VPVNP.RAMMemory

/-- In the initial record sequence, logical slot `a` installs exactly
the header value at address `a`. -/
theorem initialRecords_get {α : Type*} {S a : ℕ} (ha : a < S) (header : ℕ → α) :
    (initialRecords S header)[a]? = some (initRecord header a) := by
  simp [initialRecords, ha]

/-- The two external pins in each physical header row are its two
initialization records. The pair can follow any whole-row prefix. -/
theorem initial_paired_row {α : Type*} {S base count j : ℕ}
    (fits : 2*(base+count) ≤ S) (hj : j < count) (background x y : ℕ → α) :
    let h := interleavedHeader base count background x y
    ((initialRecords S h)[2*(base+j)]?).map Record.value = some (x j) ∧
      ((initialRecords S h)[2*(base+j)+1]?).map Record.value = some (y j) := by
  dsimp only
  rw [initialRecords_get (by omega : 2*(base+j) < S),
    initialRecords_get (by omega : 2*(base+j)+1 < S)]
  simp [initRecord, hj]

end ThreeFlat.Diagonal.TraceRowMasks

end OAI
