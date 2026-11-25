import OAI.ThreeFlat.RAM.TickNavigationEntry
import OAI.ThreeFlat.RAM.TickParameterWords

namespace OAI
/-! # Raw public and boundary bits persist across the native clock prologue -/

namespace ThreeFlat.RAM.TickNavigationEntry
open Computability.VPVNP.BurstRAM PrivateRAM TickActiveROM Diagonal.TickChronology Diagonal.ApproximateImage
open scoped Fin.CommRing

variable {w a q nt ns np : ℕ}

theorem before_scratch (B : Layout) (clock : Clock) (team step : ℕ) (m : Memory w) (j : ℕ)
    (lo : j < B.control) (order : B.control+4 ≤ B.clockWords) (fit : B.clockWords < 2^w) :
    input B clock team step m j=m j := by
  rw [input,fillSegment,ite_eq_right (by omega)]
  apply TickControlHeader.store_outside
  intro i
  have hi := i.isLt
  change j ≠ ((B.control+i.val : ℕ) : Word w).val
  rw [Fin.val_cast_of_lt (by omega)]
  omega

/-- The actual memory passed to the first compressor instruction supplies each
parameter bit to its big-endian packer without reading any of the advice bits. -/
theorem parameters_at (B : Layout) (clock : Clock) (D : Fin q → Bool) (team step : ℕ)
    (par : Fin np → Bool) (oa na oc nc : Fin a → Bool) (offset len : ℕ) (word : ℕ → Word w)
    (room : offset+w*len ≤ np) (low : 2+q+nt+ns+np ≤ B.control)
    (order : B.control+4 ≤ B.clockWords) (fit : B.clockWords < 2^w) (i : ℕ) (hi : i<len)
    (j : ℕ) (hj : j<w) :
    let params := TickParameterWords.mount offset len word par
    let fields' := fields D (digits team nt) (digits step ns) params oa na oc nc
    let src := 2+q+nt+ns+offset
    input B clock team step (TickMountedPins.memory (w:=w) fields') (src+w*i+j) =
      (((word i).val.testBit (w-1-j)).toNat : Word w) := by
  intro params pins src
  have m := Nat.mul_le_mul_left w hi
  rw [Nat.mul_succ] at m
  rw [before_scratch _ _ _ _ _ _ (by dsimp [src]; omega) order fit]
  exact TickParameterWords.source D (digits team nt) (digits step ns) par oa na oc nc
    offset len word room i hi j hj

end ThreeFlat.RAM.TickNavigationEntry

end OAI
