import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.RAMRecords

/-!
# Bounded incidence lists in the descriptor scans

The third scan of Appendix E appends old-position and role identifiers to bounded lists at
their new owners. In the first scan the same operation records members of each wire bundle.
The arrays store the count and the contiguous identifier slots separately. The code below
executes one insertion in the burst RAM. Its three external probes and seven instructions
are independent of the payload width described by the identifier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- The caller supplies the count-cell address, the first row address, the slot capacity and
the identifier in registers 0–3. Registers 4–6 hold the count, slot address and unit. -/
def appendRecord {k : ℕ} : List (Op 7 k) :=
  [.read 4 0, .guardLt 4 2, .binary .add 5 1 4, .write 5 3,
    .constant 6 1, .binary .add 4 4 6, .write 0 4]

variable {w : ℕ}

theorem appendRecord_trace {k : ℕ} (pub : Fin k → Word w) (state : Word w)
    (regs : Regs w 7) (mem : Memory w) (hcap : mem (regs 0).val < regs 2) :
    let length := mem (regs 0).val
    let slot := regs 1 + length
    let after := writeMemory (writeMemory mem slot (regs 3)) (regs 0) (length + 1)
    ∃ es rs, trace pub state appendRecord regs mem = some (es, rs, after) ∧
      countProbes es = 3 ∧ es.length = 7 ∧ rs 4 = length + 1 := by
  simp (config := { decide := true }) [appendRecord, trace, Op.effect, BinaryOp.eval, hcap,
    Function.update, countProbes]
  exact ⟨rfl, rfl⟩

theorem appendRecord_full {k : ℕ} (pub : Fin k → Word w) (state : Word w)
    (regs : Regs w 7) (mem : Memory w) (hcap : ¬mem (regs 0).val < regs 2) :
    trace pub state appendRecord regs mem = none := by
  simp (config := { decide := true }) [appendRecord, trace, Op.effect, hcap, Function.update]

/-- Array state at one owner. Only the prefix below its stored length is meaningful. -/
def rowRepresents (mem : Memory w) (count row : Word w) (xs : List (Word w)) : Prop :=
  (mem count.val).val = xs.length ∧ ∀ i : Fin xs.length, mem (row.val + i.val) = xs[i.val]

/-- Under the row address bounds, the post-state represents the old list followed by the
new identifier, in the order in which the outer scan visits its incidences. -/
theorem appendRecord_represents {mem : Memory w} {count row cap value : Word w}
    {xs : List (Word w)} (hrep : rowRepresents mem count row xs)
    (hcap : xs.length < cap.val) (hfit : row.val + cap.val ≤ 2 ^ w)
    (hdisjoint : count.val < row.val ∨ row.val + cap.val ≤ count.val) :
    rowRepresents
      (writeMemory (writeMemory mem (row + mem count.val) value)
        count (mem count.val + 1)) count row (xs ++ [value]) := by
  obtain ⟨hlen, hvals⟩ := hrep
  have hadd : (row + mem count.val).val = row.val + xs.length := by
    rw [Fin.val_add, hlen, Nat.mod_eq_of_lt (by omega)]
  have hplus : (mem count.val + 1).val = xs.length + 1 := by
    have hv := cap.isLt
    have h1 : 1 % (2^w) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_one' _, h1, hlen, Nat.mod_eq_of_lt (by omega)]
  constructor
  · simp [writeMemory, hplus]
  · intro i
    have hi : i.val < xs.length + 1 := by simpa using i.isLt
    have hne : row.val + i.val ≠ count.val := by omega
    simp only [writeMemory, ite_eq_right hne]
    by_cases hpre : i.val < xs.length
    · have hx : row.val + i.val ≠ (row + mem count.val).val := by omega
      rw [ite_eq_right hx, List.getElem_append_left hpre]
      exact hvals ⟨i.val, hpre⟩
    · have hi' : i.val = xs.length := by omega
      have he : row.val + i.val = (row + mem count.val).val := by omega
      rw [ite_eq_left he, List.getElem_append_right (by omega)]
      simp [hi']

/-- Executing the fixed instruction table returns the new length in the persistent state. -/
theorem appendRecord_native {k : ℕ} (pub : Fin k → Word w) (state : Word w) (regs : Regs w 7)
    (priv : Word w → Word w) (mem : Memory w) (hcap : mem (regs 0).val < regs 2) :
    let M := (template appendRecord 4).instantiate w pub
    ∃ es, execute M.program 8 ⟨M.entry, state, regs, priv⟩ mem [] =
        some ⟨es, some (mem (regs 0).val + 1)⟩ ∧ countProbes es = 3 ∧ es.length = 7 := by
  obtain ⟨es, rs, ht, hprobes, hlen, hreg⟩ := appendRecord_trace pub state regs mem hcap
  refine ⟨es, ?_, hprobes, hlen⟩
  change execute ((template appendRecord 4).instantiate w pub).program (1 + (appendRecord (k := k)).length)
    _ mem [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hreg]

end CompressorRecords

end VPVNP
end Computability
end OAI
