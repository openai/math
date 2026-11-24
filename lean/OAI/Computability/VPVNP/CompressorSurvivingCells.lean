import OAI.Computability.VPVNP.CompressorShrinkSliceSweep

/-!
# Cells written for each subdivision of a surviving wire

Every piece writes its own width, offset, interval frame and references. The
source width and source directory header are shared across all pieces. These
repeated writes agree, even when the source width is zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep.SurvivingCells

open BurstRAM SliceSchedule Compression

variable {w b q j k : ℕ} {r : Row w}

/-- The thirteen write destinations for piece `j` in a surviving row. -/
def address (r : Row w) (j : ℕ) : Fin 13 → ℕ :=
  let B := r.bank.val
  let q := r.count.val
  let a := frameHead B 1 q
  ![r.total.val, r.dst.val+j, B, B+1, B+2, B+3+j, B+3+q, B+4+q+j,
    a+3*j, a+3*j+1, a+3*j+2, a+3*q+j, a+4*q+j]

/-- The balanced width, prefix, and adjacency data written by piece `j`. -/
def value (b q j : ℕ) : Fin 13 → ℕ :=
  let width := b/q + (if j < b%q then 1 else 0)
  let start := j*(b/q) + min j (b%q)
  ![b, width, b, b, min b q, if j < min b q then 1 else 0, 0, start,
    start, 0, width, j, j]

theorem value_fit (hb : b < 2^w) (hq : q < 2^w) (hj : j < q) (f : Fin 13) :
    value b q j f < 2^w := by
  have hwidth := Finset.single_le_sum (f := splitWidth b q) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ (⟨j,hj⟩ : Fin q))
  rw [sum_splitWidth b q (Nat.zero_lt_of_lt hj)] at hwidth
  have hpiece : b/q + (if j < b%q then 1 else 0) ≤ b := by
    by_cases h : j < b%q <;> simpa [splitWidth, h] using hwidth
  have hstart : j*(b/q) + min j (b%q) ≤ b := by
    have := Nat.mul_le_mul_right (b/q) hj.le
    have := Nat.div_add_mod b q
    omega
  fin_cases f <;> dsimp [value] <;> first | omega | split <;> omega

theorem address_fit (space : Workspace r.total r.dst r.bank 1 r.count.val)
    (hj : j < r.count.val) (f : Fin 13) : address r j f < 2^w := by
  have := r.total.isLt
  have := space.newFit
  have := space.fits
  simp only [stop, frameHead, one_mul] at this
  fin_cases f <;> dsimp [address, frameHead] <;> omega

theorem inside (hj : j < r.count.val) (f : Fin 13) : ¬ r.Outside (address r j f) := by
  fin_cases f <;> dsimp [address, Row.Outside, frameHead, stop] <;> omega

set_option maxHeartbeats 2500000 in
/-- Disjoint header columns and endpoint arrays determine the field number
uniquely. The three interleaved frame columns differ modulo three. -/
private theorem same_field (space : Workspace r.total r.dst r.bank 1 r.count.val)
    (apart : r.total.val < r.dst.val ∨ r.dst.val+r.count.val ≤ r.total.val)
    (hj : j < r.count.val) (hk : k < r.count.val) {f g : Fin 13}
    (e : address r j f = address r k g) : f = g := by
  have ht := space.oldApart
  have hd := space.newApart
  simp only [stop, frameHead, one_mul] at ht hd
  fin_cases f <;> fin_cases g <;> first
    | rfl
    | dsimp [address, frameHead] at e
      omega

theorem address_injective (space : Workspace r.total r.dst r.bank 1 r.count.val)
    (apart : r.total.val < r.dst.val ∨ r.dst.val+r.count.val ≤ r.total.val)
    (hj : j < r.count.val) : Function.Injective (address r j) := by
  intro f g e
  exact same_field space apart hj hj e

/-- Two writes in the same row can only collide within the same column.
For a piece-specific column the address then determines the piece, and for a
shared header column the value depends only on the row. -/
theorem same_value (space : Workspace r.total r.dst r.bank 1 r.count.val)
    (apart : r.total.val < r.dst.val ∨ r.dst.val+r.count.val ≤ r.total.val)
    (hj : j < r.count.val) (hk : k < r.count.val) {f g : Fin 13}
    (e : address r j f = address r k g) :
    value b r.count.val j f = value b r.count.val k g := by
  have he := same_field space apart hj hk e
  subst g
  fin_cases f <;> dsimp [address, value] at e ⊢ <;> first
    | rfl
    | rw [show j = k by omega]

end CompressorRecords.ShrinkSliceSweep.SurvivingCells

end VPVNP
end Computability
end OAI
