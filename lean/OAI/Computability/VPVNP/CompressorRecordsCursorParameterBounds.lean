import OAI.Computability.VPVNP.CompressorRecordsCursorParameters

/-!
# Integer bounds for producing the cursor parameter frame

A single length threshold permits every split of the virtual address into
base and lane bits. The same live RAM word holds the eight public inputs,
the intermediates of the width calculation, and the exclusive ends of the
parameter frame, scheduler row and six incidence columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CursorRAM.ParametersInit

open CursorBounds Compression Filter BurstRAM

/-- Natural values of the eight public words of the parameter initializer. -/
def inputValues (n r a l row tag start frame : ℕ) : Fin 8 → ℕ :=
  ![n, r, a, l, row, tag, start, frame]

/-- The successive integer values of the straight-line width computation. -/
def widthOperands (r D H : ℕ) : List ℕ :=
  [1, 2, 4, 8, 10, r+10, (r+10)^2, (r+10)^4, D+1, (D+1)*10, (D+1)*10*H,
   (D+1)*10*H+8, ((D+1)*10*H+8)*D, ((D+1)*10*H+8)*D*(r+10)^4]

private theorem widthOperands_lt {r D H : ℕ} (hD : 0 < D) (hH : 0 < H)
    (hfit : ((D+1)*10*H+8)*D*(r+10)^4 < 2^((r+10)^4)) :
    ∀ x ∈ widthOperands r D H, x < 2^((r+10)^4) := by
  have hsquare : r+10 ≤ (r+10)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < r+10 by omega) (by decide : 1 ≤ 2)
  have hfourth := Nat.pow_le_pow_right (show 0 < r+10 by omega) (by decide : 2 ≤ 4)
  have hword := Nat.lt_two_pow_self (n := (r+10)^4)
  have hten := Nat.le_mul_of_pos_right (D+1) (by decide : 0 < 10)
  have hbucket := Nat.le_mul_of_pos_right ((D+1)*10) hH
  have hcursor := Nat.le_mul_of_pos_right ((D+1)*10*H+8) hD
  have hbits := Nat.le_mul_of_pos_right (((D+1)*10*H+8)*D) (show 0 < (r+10)^4 by positivity)
  intro x hx
  simp only [widthOperands, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst x <;> omega

/-- Simultaneous bounds at one length, with the actual frame and directory offsets. -/
structure Capacity (B n a l row tag start frame : ℕ) : Prop where
  length_ge : 3 ≤ n
  split : virtualBits B n-l+l = virtualBits B n
  cursors : 1 < virtualBits B n
  degree_lt : a < wordBits B n
  siteBits_lt : virtualBits B n < wordBits B n
  public_lt : ∀ i, inputValues n (addressBits B n) a l row tag start frame i < 2^wordBits B n
  width_lt : initialWidth B n < 2^wordBits B n
  suffix_lt : ∀ x ∈ widthOperands (addressBits B n) (virtualBits B n) (virtualBucket n),
    x < 2^wordBits B n
  frame_end : frame + 8 < 2^wordBits B n
  row_end : row + 14 < 2^wordBits B n
  arrays_end : start + 6 * rowCount (virtualBits B n-l) l a < 2^wordBits B n
  scan_end : start + 7 * rowCount (virtualBits B n-l) l a ≤ 2^wordBits B n

/-- Each shift in the parameter suffix yields its full integer power of two. -/
theorem Capacity.shiftResults_lt {B n a l row tag start frame : ℕ}
    (h : Capacity B n a l row tag start frame) :
    2^a < 2^wordBits B n ∧ 2^(virtualBits B n-l) < 2^wordBits B n ∧ 2^l < 2^wordBits B n := by
  have hD := h.siteBits_lt
  have hl := h.split
  exact ⟨Nat.pow_lt_pow_right Nat.one_lt_two h.degree_lt,
    Nat.pow_lt_pow_right Nat.one_lt_two (by omega), Nat.pow_lt_pow_right Nat.one_lt_two (by omega)⟩

/-- For fixed address and degree exponents and polynomially bounded frame and
directory locations, one threshold works for every admissible lane exponent. -/
theorem eventually_capacity (B a : ℕ) (hB : 1 ≤ B) {row tag start frame : ℕ → ℕ}
    (hr : PolynomiallyBounded row) (ht : PolynomiallyBounded tag)
    (hs : PolynomiallyBounded start) (hf : PolynomiallyBounded frame) :
    ∀ᶠ n : ℕ in atTop, ∀ l ≤ virtualBits B n, Capacity B n a l (row n) (tag n) (start n) (frame n) := by
  filter_upwards [eventually_ge_atTop 3, eventually_cursorCapacity B a hB hs,
    eventual_word_room B hB PolynomiallyBounded.id, eventual_word_room B hB ht,
    eventual_word_room B hB (hr.add (PolynomiallyBounded.const 14)),
    eventual_word_room B hB (hf.add (PolynomiallyBounded.const 8))] with n hn hc hnfit htfit hrfit hffit
  intro l hl
  let D := virtualBits B n
  let b := D-l
  let w := wordBits B n
  have split : b+l = D := Nat.sub_add_cancel hl
  obtain ⟨hD, _, hwfit, hcost⟩ := hc b l split
  rw [split] at hD
  have count := rowCount_eq_positions split a
  change rowCount b l a = 2^D * D * 2^a at count
  have hpos := Nat.zero_lt_one.trans hD
  have hsitesPos := Nat.mul_pos (Nat.two_pow_pos D) hpos
  have hp : 0 < rowCount b l a := count ▸ Nat.mul_pos hsitesPos (Nat.two_pow_pos a)
  have hend : start n + 6 * rowCount b l a < 2^w :=
    (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (by decide : 6 < 7) hp) _).trans_le hcost
  have hrows : rowCount b l a < 2^w :=
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 6)).trans_lt ((Nat.le_add_left ..).trans_lt hend)
  have hsites : 2^D ≤ rowCount b l a := by
    rw [count]
    exact (Nat.le_mul_of_pos_right _ hpos).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))
  have hdegree : 2^a ≤ rowCount b l a := by
    rw [count]; exact Nat.le_mul_of_pos_left _ hsitesPos
  have site_lt := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (hsites.trans_lt hrows)
  have degree_lt := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (hdegree.trans_lt hrows)
  have hw := Nat.lt_two_pow_self (n := w)
  have hrD : addressBits B n ≤ D := addressBits_le_virtualBits B n hn
  change row n + 14 < 2^w at hrfit
  change frame n + 8 < 2^w at hffit
  change n < 2^w at hnfit
  change tag n < 2^w at htfit
  refine ⟨hn, split, hD, degree_lt, site_lt, ?_, hwfit, ?_, hffit, hrfit, hend, hcost⟩
  · intro i
    fin_cases i
    · exact hnfit
    · exact hrD.trans_lt (site_lt.trans hw)
    · exact degree_lt.trans hw
    · exact hl.trans_lt (site_lt.trans hw)
    · exact (Nat.le_add_right ..).trans_lt hrfit
    · exact htfit
    · exact (Nat.le_add_right ..).trans_lt hend
    · exact (Nat.le_add_right ..).trans_lt hffit
  · rw [initialWidth, arc_width] at hwfit
    exact widthOperands_lt hpos (Nat.two_pow_pos _) hwfit

/-- The public parameter vector for the native initializer, in live-width words. -/
def publicInputs (B n a l row tag start frame : ℕ) : Fin 8 → Word (wordBits B n) :=
  fun i ↦ encode (wordBits B n) (inputValues n (addressBits B n) a l row tag start frame i)

theorem Capacity.publicInputs_val {B n a l row tag start frame : ℕ}
    (h : Capacity B n a l row tag start frame) (i : Fin 8) :
    (publicInputs B n a l row tag start frame i).val =
      inputValues n (addressBits B n) a l row tag start frame i :=
  Nat.mod_eq_of_lt (h.public_lt i)

/-- The two native bursts install the scheduler row from encoded public inputs
at every sufficiently large length. The threshold is independent of the lane
split, the entry state and the initial contents of memory. -/
theorem eventually_scheduler_prefix (B a : ℕ) (hB : 1 ≤ B) {row tag start frame : ℕ → ℕ}
    (hr : PolynomiallyBounded row) (ht : PolynomiallyBounded tag)
    (hs : PolynomiallyBounded start) (hf : PolynomiallyBounded frame) :
    ∀ᶠ n : ℕ in atTop, ∀ l ≤ virtualBits B n, ∀ (state : Word (wordBits B n)) (m : Memory (wordBits B n)),
      PrefixCorrect (publicInputs B n a l (row n) (tag n) (start n) (frame n)) state m B n a l := by
  filter_upwards [eventually_capacity B a hB hr ht hs hf] with n hc
  intro l hl state m
  have h := hc l hl
  apply scheduler_prefix state m hB ((by decide : 2 ≤ 3).trans h.length_ge) rfl
    (h.publicInputs_val 0) (h.publicInputs_val 1) (h.publicInputs_val 2) (h.publicInputs_val 3)
    h.degree_lt hl
  · rw [h.publicInputs_val]; exact h.frame_end.le
  · rw [h.publicInputs_val]; exact h.row_end.le

end CompressorRecords.CursorRAM.ParametersInit

end VPVNP
end Computability
end OAI
