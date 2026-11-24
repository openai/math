import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The cut widths in the paired chain

The primary paper uses a chain of length `2^H`. Equation (9.1) allocates
`(H − ⌊log₂ i⌋) Δ` bits to the interior cut numbered `i`. On the first half
this is exactly the width of the doubled primed cut plus one block. On the
tail there is one block. The field layouts below keep the mode at the first
position and the zero padding at the end.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CutSchedule

/-- Number of bits on a cut, with both missing endpoint cuts clamped. -/
def width (H Δ i : ℕ) : ℕ :=
  if 0 < i ∧ i < 2 ^ H then (H - Nat.log 2 i) * Δ else 0

@[simp] theorem width_zero (H Δ : ℕ) : width H Δ 0 = 0 := by simp [width]

@[simp] theorem width_end (H Δ : ℕ) : width H Δ (2 ^ H) = 0 := by simp [width]

/-- On every nonempty cut in the tail, including the middle cut, the width is one block. -/
theorem width_tail (h Δ i : ℕ) (hi : 2 ^ h ≤ i) (hlt : i < 2 ^ (h + 1)) :
    width (h + 1) Δ i = Δ := by
  have hi' : 0 < i := (Nat.two_pow_pos h).trans_le hi
  rw [width, ite_eq_left ⟨hi', hlt⟩, Nat.log_eq_of_pow_le_of_lt_pow hi hlt]
  simp

/-- Doubling the primed cut number saves exactly one block, even at the
middle cut where the doubled primed cut is the empty endpoint. -/
theorem width_double (h Δ i : ℕ) (hi : 0 < i) (hle : i ≤ 2 ^ h) :
    width (h + 1) Δ i = width (h + 1) Δ (2 * i) + Δ := by
  have hh : 0 < 2 ^ h := Nat.two_pow_pos h
  have hi' : i < 2 ^ (h + 1) := by rw [pow_succ]; omega
  by_cases he : i = 2 ^ h
  · subst i
    rw [width_tail _ _ _ le_rfl hi', ← pow_succ', width_end, Nat.zero_add]
  · have h2i : 2 * i < 2 ^ (h + 1) := by rw [pow_succ]; omega
    have hlog := Nat.log_lt_of_lt_pow (Nat.ne_of_gt hi) hi'
    rw [width, width, ite_eq_left ⟨hi, hi'⟩, ite_eq_left ⟨by omega, h2i⟩, Nat.mul_comm 2 i,
      Nat.log_mul_base (by decide) (Nat.ne_of_gt hi)]
    rw [show h + 1 - Nat.log 2 i = (h + 1 - (Nat.log 2 i + 1)) + 1 by omega, Nat.succ_mul]

/-- A width-`w` Boolean word indexed by the integers from zero to `w - 1`. -/
abbrev Bits (w : ℕ) := Fin w → Bool

/-- Split a cut into its contiguous left and right fields. -/
def splitBits (a b : ℕ) : Bits (a + b) ≃ Bits a × Bits b :=
  (finSumFinEquiv.symm.arrowCongr (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) Bool)

private def castBits {a b : ℕ} (h : a = b) : Bits a ≃ Bits b :=
  (finCongr h).arrowCongr (Equiv.refl Bool)

private def modeBits : Bits 1 ≃ Bool := Equiv.funUnique _ _

/-- The first-half layout in Section 14.1 in the order mode, exterior primed
bits, exponents, padding. Exponents use the RAM's fixed-width binary encoding.
A zero width gives the unique empty bit string. -/
def firstHalfLayout (h Δ i t Z : ℕ) (hi : 0 < i) (hle : i ≤ 2 ^ h) (hfit : 1 + t * Z ≤ Δ) :
    Bits (width (h + 1) Δ i) ≃
      Bool × Bits (width (h + 1) Δ (2 * i)) × (Fin t → BurstRAM.Word Z) × Bits (Δ - (1 + t * Z)) :=
  let old := width (h + 1) Δ (2 * i)
  let pad := Δ - (1 + t * Z)
  let size : width (h + 1) Δ i = 1 + (old + (t * Z + pad)) := by
    rw [width_double h Δ i hi hle]
    dsimp [old, pad]
    omega
  let splitPayload := (splitBits (t * Z) pad).trans
    ((RAMSerialization.arrayBits t Z).symm.prodCongr (Equiv.refl _))
  let splitExterior := (splitBits old _).trans ((Equiv.refl _).prodCongr splitPayload)
  (castBits size).trans ((splitBits 1 _).trans (modeBits.prodCongr splitExterior))

/-- Tail cuts store one mode, the evaluator configuration, and trailing padding. -/
def tailLayout (h Δ i c : ℕ) (hi : 2 ^ h ≤ i) (hlt : i < 2 ^ (h + 1)) (hfit : 1 + c ≤ Δ) :
    Bits (width (h + 1) Δ i) ≃ Bool × Bits c × Bits (Δ - (1 + c)) :=
  let size : width (h + 1) Δ i = 1 + (c + (Δ - (1 + c))) := by rw [width_tail _ _ _ hi hlt]; omega
  (castBits size).trans ((splitBits 1 _).trans (modeBits.prodCongr (splitBits c _)))

/-- Exterior bits and the accumulated label exponents uniquely fix each
first-half cut string once the mode and canonical zero padding are imposed. -/
theorem firstHalf_unique (h Δ i t Z : ℕ) (hi : 0 < i) (hle : i ≤ 2 ^ h) (hfit : 1 + t * Z ≤ Δ)
    (mode : Bool) (exterior : Bits (width (h + 1) Δ (2 * i))) (exponents : Fin t → BurstRAM.Word Z) :
    ∃! bits, firstHalfLayout h Δ i t Z hi hle hfit bits =
      (mode, exterior, exponents, fun _ => false) :=
  (firstHalfLayout h Δ i t Z hi hle hfit).bijective.existsUnique _

/-- The configuration and mode determine exactly one canonically padded
tail cut, also when no padding is needed. -/
theorem tail_unique (h Δ i c : ℕ) (hi : 2 ^ h ≤ i) (hlt : i < 2 ^ (h + 1)) (hfit : 1 + c ≤ Δ)
    (mode : Bool) (config : Bits c) :
    ∃! bits, tailLayout h Δ i c hi hlt hfit bits = (mode, config, fun _ => false) :=
  (tailLayout h Δ i c hi hlt hfit).bijective.existsUnique _

/-- Every prefix sum of local `2r`-bit increments fits in the paper's `Z = 2H`
bits when `2r < H`, as verified in Section 14.1. -/
theorem accumulated_lt (H r k : ℕ) (inc : ℕ → ℕ) (hk : k ≤ 2 ^ H) (hr : 2 * r < H)
    (hinc : ∀ i < k, inc i < 2 ^ (2 * r)) :
    ∑ i ∈ Finset.range k, inc i < 2 ^ (2 * H) := by
  calc
    _ ≤ ∑ _i ∈ Finset.range k, 2 ^ (2 * r) :=
      Finset.sum_le_sum (fun i hi => (hinc i (Finset.mem_range.mp hi)).le)
    _ = k * 2 ^ (2 * r) := by simp
    _ ≤ 2 ^ H * 2 ^ (2 * r) := Nat.mul_le_mul_right _ hk
    _ = 2 ^ (H + 2 * r) := (pow_add ..).symm
    _ < 2 ^ (2 * H) := Nat.pow_lt_pow_right (by decide) (by omega)

end CutSchedule

end VPVNP
end Computability
end OAI
