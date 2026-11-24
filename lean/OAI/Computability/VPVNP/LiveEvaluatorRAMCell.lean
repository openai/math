import OAI.Computability.VPVNP.LiveEvaluatorRAM
import OAI.Computability.VPVNP.LiveEvaluatorCellEquivalence

/-!
# Word-level correctness of the finite evaluator tape scan

The source-indexed tests in the fixed private-RAM template read the old
symbol and its paired destination in memory. Reading all these pairs
checks the full unbounded evaluator tape transition.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM

open BurstRAM PrimedInputRAM PrimedStackRAM UniversalMachine LiveEvaluatorEncoding LiveEvaluatorStep
open scoped Fin.CommRing

variable {w k M : ℕ}

/-- The numeric fields of one call and its two memory slices. Each bit-field
word has already been unpacked at its agreed memory address. -/
structure TapeCellData (rs : Regs w 32) (m : Memory w) (old out : TapeWindow M)
    (write move : Symbol) (i : WindowCell M) : Prop where
  zero : (rs 0).val = 0
  one : (rs 1).val = 1
  three : (rs 3).val = 3
  writeVal : (rs 6).val = write.val
  moveVal : (rs 7).val = move.val
  center : (rs 11).val = M
  last : (rs 12).val = 2 * M
  index : (rs 13).val = i.val
  oldCell : (m (rs 14 + rs 13).val).val = (old.cells i).val
  outCell : ∀ (j : BurstRAM.Word w) (f : WindowCell M), j.val = f.val →
    (m (rs 15 + j).val).val = (out.cells f).val

theorem destination_val_of_limbs (z o last mw idx : Word w) (move : Symbol) (i : WindowCell M)
    (hz₀ : z.val = 0) (h₁ : o.val = 1) (hmax : last.val = 2 * M)
    (hm : mw.val = move.val) (hi₀ : idx.val = i.val) :
    (destination z o last mw idx).val = (cellDestination move i).val := by
  have hz : mw = z ↔ move = 0 := by simp only [Fin.ext_iff, hm, hz₀, Fin.val_zero]
  have ho : mw = o ↔ move = 1 := by simp only [Fin.ext_iff, hm, h₁]; rfl
  have hl : idx = last ↔ i.val = 2 * M := by simp only [Fin.ext_iff, hi₀, hmax]
  have hi : idx = z ↔ i.val = 0 := by simp only [Fin.ext_iff, hi₀, hz₀]
  simp only [destination, cellDestination, hz, ho, hl, hi]
  split_ifs <;> try first | exact hi₀ | exact hz₀ | exact hmax
  · rw [Fin.val_add_eq_of_add_lt, hi₀, h₁]
    have := (last).isLt
    rw [hmax] at this
    rw [hi₀, h₁]
    omega
  · rw [Fin.sub_val_of_le, hi₀, h₁]
    change (o).val ≤ (idx).val
    rw [hi₀, h₁]
    omega

private theorem destination_val (rs : Regs w 32) (m : Memory w) (old out : TapeWindow M)
    (write move : Symbol) (i : WindowCell M) (h : TapeCellData rs m old out write move i) :
    (destination (rs 0) (rs 1) (rs 12) (rs 7) (rs 13)).val = (cellDestination move i).val :=
  destination_val_of_limbs _ _ _ _ _ _ _ h.zero h.one h.last h.moveVal h.index

private theorem clipped_iff (rs : Regs w 32) (m : Memory w) (old out : TapeWindow M)
    (write move : Symbol) (i : WindowCell M) (h : TapeCellData rs m old out write move i) :
    clipped (rs 0) (rs 1) (rs 12) (rs 7) (rs 13) ↔ cellClipped move i := by
  simp only [clipped, cellClipped, ne_eq, Fin.ext_iff, h.zero, h.one, h.last, h.moveVal, h.index, Fin.val_zero]; rfl

theorem cellTest_running_iff {rs : Regs w 32} {m : Memory w} {old out : TapeWindow M}
    {write move : Symbol} {i : WindowCell M} (h : TapeCellData rs m old out write move i)
    (hs : rs 16 ≠ rs 1) (ht : rs 5 ≠ rs 1) :
    cellTest rs m ↔ (cellClipped move i → writtenSymbol old write i = 0) ∧
      out.cells (cellDestination move i) = writtenSymbol old write i := by
  have hlt : m (rs 14 + rs 13).val < rs 3 := by
    change (m (rs 14 + rs 13).val).val < (rs 3).val
    rw [h.oldCell, h.three]
    exact (old.cells i).isLt
  have hc : rs 13 = rs 11 ↔ i.val = M := by simp [Fin.ext_iff, h.index, h.center]
  have hd := h.outCell _ _ (destination_val _ _ _ _ _ _ _ h)
  simp only [cellTest, ite_eq_right hs, ite_eq_right ht, hlt, true_and]
  simp only [clipped_iff _ _ _ _ _ _ _ h, writtenSymbol, hc]
  split_ifs <;> simp only [Fin.ext_iff, h.zero, h.writeVal, h.oldCell, hd, Fin.val_zero]

/-- Each native fragment exits precisely on a matching symbol pair. All
fragments together check both endpoints and every proposed tape cell. -/
theorem tapeScan_exec_iff (pub : Fin k → BurstRAM.Word w) (state : BurstRAM.Word w)
    (m : Memory w) (old out : TapeWindow M) (write move : Symbol) (rs : WindowCell M → Regs w 32)
    (h : ∀ i, TapeCellData (rs i) m old out write move i)
    (hs : ∀ i, rs i 16 ≠ rs i 1) (ht : ∀ i, rs i 5 ≠ rs i 1) :
    (∀ i, ∃ es regs mem, Flow.Exec pub state cell (rs i) m es regs mem) ↔
      boundaryBlank old write move = true ∧ out = updatedWindow old write move := by
  rw [← cellChecks_iff]
  exact forall_congr' fun i => (cell_exec_iff ..).trans (cellTest_running_iff (h i) (hs i) (ht i))

end LiveEvaluatorRAM

end VPVNP
end Computability
end OAI
