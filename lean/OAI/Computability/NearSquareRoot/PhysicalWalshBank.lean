import OAI.Computability.IntegerMultiplication.Code.Slice
import Mathlib.Data.List.OfFn

/-! # Bank layout for parallel Walsh programs

Each packet starts with a shared header. The parallel instruction divides its
rows into two consecutive groups and gives a copy of the header to each
subprogram. The two outputs are reassembled in program order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshBank

open IntegerMultiplication.Code

variable {H R : Type*}

/-- Split after the first `i` complete rows in a single bank. -/
def split (i : ℕ) (a : H × List R) : (H × List R) × (H × List R) :=
  ((a.1, a.2.take i), (a.1, a.2.drop i))

/-- Reassemble the two output banks of a parallel program. -/
def combine (p : (H × List R) × (H × List R)) : H × List R :=
  (p.1.1, p.1.2 ++ p.2.2)

theorem easy_split [Codec H] [Codec R] (i : ℕ) : Easy (split (H := H) (R := R) i) := by
  have cut : Easy (fun a : H × List R => cutLists (tally i, a.2)) :=
    easy_cut ((Easy.const (tally i)).pair Easy.snd)
  unfold split
  simpa only [cutLists, tally_length] using
    (Easy.fst.pair (cut.compose Easy.fst)).pair (Easy.fst.pair (cut.compose Easy.snd))

theorem easy_combine [Codec H] [Codec R] : Easy (combine (H := H) (R := R)) := by
  unfold combine
  fun_prop

theorem split_rows {i j : ℕ} (h : H) (x : Fin i → R) (y : Fin j → R) :
    split i (h, List.ofFn (Fin.append x y)) = ((h, List.ofFn x), (h, List.ofFn y)) := by
  simp [split, List.ofFn_fin_append]

theorem combine_rows {i j : ℕ} (h h' : H) (x : Fin i → R) (y : Fin j → R) :
    combine ((h, List.ofFn x), (h', List.ofFn y)) = (h, List.ofFn (Fin.append x y)) := by
  simp [combine, List.ofFn_fin_append]

/-- Bounds the full row bank, including each list constructor and the final delimiter. -/
theorem size_rows_le [Codec R] {i : ℕ} (rows : Fin i → R) (b : ℕ)
    (h : ∀ j, size (rows j) ≤ b) :
    size (List.ofFn rows) ≤ i * (b + 1) + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h₀ := h 0
    have hs := ih (fun j => rows j.succ) (fun j => h j.succ)
    rw [List.ofFn_succ, size_cons, Nat.succ_mul]
    omega

/-- A bank of `i` rows of `n` records each, with `b` symbols per record. -/
theorem size_cells_le [Codec R] {i n : ℕ} (cells : Fin i → Fin n → R) (b : ℕ)
    (h : ∀ j c, size (cells j c) ≤ b) :
    size (List.ofFn (fun j => List.ofFn (cells j))) ≤ i * (n * (b + 1) + 2) + 1 :=
  size_rows_le _ (n * (b + 1) + 1) (fun j => size_rows_le (cells j) b (h j))

end PhysicalWalshBank

end NearSquareRoot
end Computability
end OAI
