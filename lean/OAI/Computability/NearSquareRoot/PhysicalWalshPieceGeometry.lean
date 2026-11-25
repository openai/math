import OAI.Computability.NearSquareRoot.PhysicalWalshNode
import OAI.Computability.NearSquareRoot.WalshPadding
import OAI.Computability.NearSquareRoot.WalshPieces

/-! # Ordered headers for the even Walsh pieces

At digit position `j`, the lower digits occupy twice the remainder modulo
`A^j` selected bits. Each of the next pieces consumes another `2*A^j` bits.
Both spectator counts in the resulting header refer to the same padded array.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open PhysicalWalshNode

/-- Base-`A` digit giving the number of pieces at level `j`. -/
def digit (A s j : ℕ) := (s/2 / A^j) % A

/-- Number of selected bits before repetition `t` of digit `j`. -/
def offset (A s j t : ℕ) := 2*((s/2) % A^j) + t*(2*A^j)

theorem digit_eq_get {A : ℕ} (hA : 1 < A) (s : ℕ) (j : Fin (walshPieceDigits A s).length) :
    digit A s j = (walshPieceDigits A s).get j := by
  rw [digit, ← Nat.getD_digits _ _ hA]
  change (walshPieceDigits A s).getD _ _ = _
  exact List.getD_eq_get _ _ j

theorem offset_succ (A s j t : ℕ) :
    offset A s j (t+1) = offset A s j t + grow A j := by
  unfold offset grow
  ring

theorem offset_next (A s j : ℕ) :
    offset A s j (digit A s j) = offset A s (j+1) 0 := by
  simp only [offset, digit, pow_succ, Nat.mod_mul, zero_mul, add_zero]
  ring

@[simp] theorem offset_first (A s : ℕ) : offset A s 0 0 = 0 := by simp [offset, Nat.mod_one]

theorem offset_end {A : ℕ} (hA : 1 < A) (s : ℕ) :
    offset A s (walshPieceDigits A s).length 0 = 2*(s/2) := by
  have h : s/2 < A^(walshPieceDigits A s).length := Nat.lt_base_pow_length_digits hA
  simp [offset, Nat.mod_eq_of_lt h]

theorem offset_add_grow_le {A s j t : ℕ} (ht : t < digit A s j) :
    offset A s j t + grow A j ≤ s := by
  have h := Nat.mul_le_mul_left (A^j) (ht.trans_le (Nat.mod_le (s/2 / A^j) A))
  change A^j*(t+1) ≤ A^j*(s/2 / A^j) at h
  have h' := Nat.mod_add_div (s/2) (A^j)
  calc
    offset A s j t + grow A j = 2 * ((s/2) % A^j + A^j*(t+1)) := by unfold offset grow; ring
    _ ≤ 2*(s/2) := Nat.mul_le_mul_left 2 (by omega)
    _ ≤ s := by omega

/-- The active piece lies between the leading spectator and trailing bit fields. -/
def shape (A W : ℕ) (hW : 0 < W) (k s w j t : ℕ) : Shape where
  level := j
  pref := WalshPadding.paddedRows (2^(k-s)) W (WalshPadding.depth A s) * 2^offset A s j t
  suff := 2^(s-offset A s j t-grow A j)
  w := w
  pref_pos := Nat.mul_pos ((Nat.two_pow_pos _).trans_le (WalshPadding.rows_le_paddedRows hW)) (by positivity)
  suff_pos := Nat.two_pow_pos _

/-- Positions run in increasing order, with repetitions consecutive. -/
def schedule (A W : ℕ) (hW : 0 < W) (k s w : ℕ) : List Shape :=
  (List.ofFn fun j : Fin (walshPieceDigits A s).length =>
    List.ofFn fun t : Fin (digit A s j) => shape A W hW k s w j t).flatten

theorem count_shape {A W : ℕ} (hW : 0 < W) (k s w j t : ℕ) (ht : t < digit A s j) :
    count A (shape A W hW k s w j t) =
      WalshPadding.paddedRows (2^(k-s)) W (WalshPadding.depth A s) * 2^s := by
  have h := offset_add_grow_le ht
  change (_ * 2^offset A s j t) * (2^grow A j * 2^(s-offset A s j t-grow A j)) = _
  rw [Nat.mul_assoc, ← pow_add, ← pow_add, show offset A s j t +
    (grow A j + (s-offset A s j t-grow A j)) = s by omega]

theorem pref_dvd {A W : ℕ} (hA : 1 < A) (hW : 0 < W) (k s w : ℕ)
    (j : Fin (walshPieceDigits A s).length) (t : ℕ) :
    W^j.val ∣ (shape A W hW k s w j t).pref := by
  have hj := (Nat.lt_digits_length_iff hA _).mp j.isLt
  have hd : j.val ≤ WalshPadding.depth A s := Nat.le_log_of_pow_le hA hj
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow W hd) _) _

theorem mem_schedule {A W : ℕ} (hW : 0 < W) (k s w : ℕ) (z : Shape) :
    z ∈ schedule A W hW k s w ↔ ∃ (j : Fin (walshPieceDigits A s).length) (t : Fin (digit A s j)),
      shape A W hW k s w j t = z := by
  simp [schedule, List.mem_flatten, List.mem_ofFn]

/-- Sum any level-dependent expense over the physically emitted list in digit order. -/
theorem schedule_sum {A W : ℕ} (hA : 1 < A) (hW : 0 < W) (k s w : ℕ) (f : ℕ → ℝ) :
    ((schedule A W hW k s w).map (fun p => f p.level)).sum =
      ∑ j : Fin (walshPieceDigits A s).length, ((walshPieceDigits A s).get j : ℝ)*f j := by
  simp only [schedule, List.map_flatten, List.sum_flatten, List.map_ofFn, Function.comp_def,
    List.sum_ofFn, shape, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    digit_eq_get hA]

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
