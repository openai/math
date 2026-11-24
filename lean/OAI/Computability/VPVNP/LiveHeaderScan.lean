import OAI.Computability.VPVNP.LiveHeaderBits
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Log

/-!
# Streaming the long live group index

The one-based group number can have polynomially many bits. Each burst reads
one bit at its processor, appends it to the scratch array, and updates the
index of the last set bit and the number of set bits. At completion these two
word-sized statistics give its base-two logarithm and the power-of-two test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Positions of the set bits observed before the next cursor. -/
def prefixOnes (index cursor : ℕ) : Finset ℕ :=
  (Finset.range cursor).filter (fun k => index.testBit k)

/-- Highest observed position, or zero in the empty prefix. -/
def prefixHigh (index cursor : ℕ) := (prefixOnes index cursor).sup id

theorem prefixOnes_succ (index cursor : ℕ) :
    prefixOnes index (cursor+1) = if index.testBit cursor then
      insert cursor (prefixOnes index cursor) else prefixOnes index cursor := by
  rw [prefixOnes, Finset.range_add_one, Finset.filter_insert]
  rfl

theorem prefixCount_succ (index cursor : ℕ) :
    (prefixOnes index (cursor+1)).card = (prefixOnes index cursor).card + (index.testBit cursor).toNat := by
  have hn : cursor ∉ prefixOnes index cursor := by simp [prefixOnes]
  cases h : index.testBit cursor <;> simp [prefixOnes_succ, h, hn]

theorem prefixHigh_succ (index cursor : ℕ) :
    prefixHigh index (cursor+1) = if index.testBit cursor then cursor else prefixHigh index cursor := by
  have hle : prefixHigh index cursor ≤ cursor := Finset.sup_le fun j hj =>
    (Finset.mem_range.mp (Finset.mem_filter.mp hj).1).le
  cases h : index.testBit cursor
  · simp [prefixHigh, prefixOnes_succ, h]
  · rw [prefixHigh, prefixOnes_succ, h, ite_eq_left rfl, ite_eq_left rfl, Finset.sup_insert]
    exact max_eq_left hle

/-- Once all bits have been read, the last set bit is the binary logarithm
and exactly one set bit characterizes a power of two. -/
theorem summary_correct {index length : ℕ} (hpos : index ≠ 0) (hfit : index < 2 ^ length) :
    prefixHigh index length = Nat.log 2 index ∧
      ((prefixOnes index length).card = 1 ↔ index = 2 ^ Nat.log 2 index) := by
  let k := Nat.log 2 index
  have hk : k < length := (Nat.log_lt_iff_lt_pow (by decide) hpos).mpr hfit
  have hmem : k ∈ prefixOnes index length := by
    have ht := Nat.testBit_log2 hpos
    rw [Nat.log2_eq_log_two] at ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ht⟩
  have hle (j : ℕ) (hj : j ∈ prefixOnes index length) : j ≤ k :=
    Nat.le_log_of_pow_le (by decide) (Nat.two_pow_le_of_mem_bitIndices
      (Nat.mem_bitIndices.mpr (Finset.mem_filter.mp hj).2))
  refine ⟨le_antisymm (Finset.sup_le hle) (Finset.le_sup (f := id) hmem), ?_⟩
  constructor
  · intro hc
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
    have hjk : j = k := (Finset.mem_singleton.mp (hj ▸ hmem)).symm
    subst j
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_two_pow]
    by_cases h : j < length
    · rw [Bool.eq_iff_iff, decide_eq_true_iff]
      have he := Finset.ext_iff.mp hj j
      simpa only [prefixOnes, Finset.mem_filter, Finset.mem_range, h, true_and,
        Finset.mem_singleton, eq_comm] using he
    · have hzero := Nat.testBit_lt_two_pow (hfit.trans_le (Nat.pow_le_pow_right (by decide) (by omega : length ≤ j)))
      simp [hzero, show Nat.log 2 index ≠ j from by change k ≠ j; omega]
  · intro hi
    suffices prefixOnes index length = {k} by simp [this]
    ext j
    change j ∈ (Finset.range length).filter (fun a => index.testBit a) ↔ _
    change index = 2 ^ k at hi
    rw [Finset.mem_filter, Finset.mem_range, hi, Nat.testBit_two_pow, decide_eq_true_iff, Finset.mem_singleton]
    constructor
    · exact fun h => h.2.symm
    · rintro rfl
      exact ⟨hk, rfl⟩

/-- Public words are the bit-array base, high-index cell, and population-count
cell. The persistent state is the next site address. All reads precede writes. -/
def indexCell : List (Op 12 3) :=
  [.stateWord 0] ++ fetch 0 ++
    [.publicWord 4 0, .publicWord 5 1, .publicWord 6 2, .read 7 5, .read 8 6,
      .binary .sub 9 3 1, .binary .mul 7 7 9, .binary .mul 9 0 1, .binary .add 7 7 9,
      .binary .add 8 8 1, .binary .add 4 4 0, .write 4 1, .write 5 7, .write 6 8,
      .binary .add 11 0 3]

/-- Store one group-index bit, update the highest set position if the bit is one, and add it to
the population count. -/
def indexUpdate (pub : Fin 3 → Word w) (state : Word w) (m : Memory w) (b : Bool) : Memory w :=
  let copied := writeMemory m (pub 0 + state) (PrimedInputRAM.encodeBit w b)
  let indexed := writeMemory copied (pub 1) (if b then state else m (pub 1).val)
  writeMemory indexed (pub 2) (m (pub 2).val + PrimedInputRAM.encodeBit w b)

/-- Exactly one call visits this bit. The trace has three reads, three writes,
twenty-one instructions and no branch choices. -/
theorem indexCell_trace (hw : 4 ≤ w) (pub : Fin 3 → Word w) (state : Word w)
    (rs : Regs w 12) (m : Memory w) :
    let b := (m state.val).val.testBit 0
    ∃ es rs', trace pub state indexCell rs m = some (es, rs', indexUpdate pub state m b) ∧
      rs' 11 = state + 1 ∧ es.length = 21 ∧ countProbes es = 6 ∧ choiceBits es = [] := by
  cases hb : (m state.val).val.testBit 0 <;>
    simp only [Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one, decide_eq_false_iff_not, decide_eq_true_iff] at hb <;>
    simp (config := { decide := true }) [indexCell, fetch, trace, Op.effect, Function.update,
      show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl,
      show BinaryOp.sub.eval = (· - · : Word w → Word w → Word w) from rfl,
      show BinaryOp.mul.eval = (· * · : Word w → Word w → Word w) from rfl,
      PrimedInputRAM.Opcodes.readBit_word (by omega : 0 < w), hb, PrimedInputRAM.encodeBit,
      indexUpdate, countProbes, choiceBits]

end LiveHeader

end VPVNP
end Computability
end OAI
