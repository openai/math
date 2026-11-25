import OAI.ThreeFlat.RAM.ExpressionScan
import OAI.ThreeFlat.Diagonal.CompressorNativeSweep

namespace OAI
/-! # Row and frame properties of chronological native memory scans -/

namespace ThreeFlat.RAM.HeaderScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan
open Diagonal.CompressorPacking.Native
open scoped Fin.NatCast

variable {w : ℕ}

/-- If writes to the current output segment preserve each row's meaning,
the chronological scan replaces precisely that segment by the given words. -/
theorem sweep_segment (f : Word w → Memory w → Word w) (lo hi : ℕ) (initial : Memory w)
    (row : ℕ → Word w) (stable : ∀ b : Word w, lo≤b.val → b.val<hi →
      ∀ m', agreesOutside lo hi m' initial → f b m'=row b.val)
    (a : Word w) (n : ℕ) (m : Memory w) (lower : lo≤a.val) (upper : a.val+n≤hi)
    (limit : hi<2^w) (frame : agreesOutside lo hi m initial) :
    sweep f n a m=fillSegment a.val n row m := by
  induction n generalizing a m with
  | zero => simp [sweep]
  | succ n ih =>
    have inside : a.val<hi := by omega
    have next : (a+1).val=a.val+1 := Fin.val_add_one_of_lt' (by change a.val+1<2^w; omega)
    change sweep f n (a+1) (writeMemory m a (f a m))=_
    rw [stable a lower inside m frame,fillSegment_succ,ih (a+1) (writeMemory m a (row a.val))]
    · rw [next]
    · rw [next]; omega
    · rw [next]; omega
    · intro i outside
      have neq : i≠a.val := by rcases outside with h|h <;> omega
      exact (show writeMemory m a (row a.val) i=m i by simp [writeMemory,neq]).trans (frame i outside)

/-- Agreement outside the output interval needs no condition on a row's
read addresses and holds for left-to-right state-dependent generation. -/
theorem sweep_outside (f : Word w → Memory w → Word w) (a : Word w) (n : ℕ) (m : Memory w)
    (limit : a.val+n<2^w) : agreesOutside a.val (a.val+n) (sweep f n a m) m := by
  induction n generalizing a m with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro i outside
    have next : (a+1).val=a.val+1 := Fin.val_add_one_of_lt' (by change a.val+1<2^w; omega)
    have neq : i≠a.val := by rcases outside with h|h <;> omega
    rw [sweep,ih (a+1) (writeMemory m a (f a m)) (by rw [next]; omega) i
      (by rw [next]; rcases outside with h|h <;> omega)]
    simp [writeMemory,neq]

end ThreeFlat.RAM.HeaderScan

end OAI
