import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.Computability.VPVNP.PrimedInputRAMHeaders

/-!
# Sparse initialization of the auxiliary pair counter

The live group stores the prescribed §11 header in a separate area of its
external memory. Only the cut lengths, index bits, advice bits, actual exterior
bits and nominated histogram words are written. The two exterior fields use
fixed capacities for addressing even when an endpoint has an empty cut.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveAuxiliaryHeaders

open BurstRAM PrimedInputRAM

variable {w : ℕ}

/-- Offset of the first exterior field after the three lengths, indices and advice. -/
def exteriorBase (L : Lengths) := 3 + 2 * L.index + L.advice

/-- Reserved header prefix, including padding in both exterior fields. -/
def span (L : Lengths) (labels : ℕ) := Header.count L + labels

private def block {N : ℕ} (start len : ℕ) (fit : start + len ≤ N) : List (Fin N) :=
  List.ofFn fun i : Fin len ↦ ⟨start + i.val, (Nat.add_lt_add_left i.isLt start).trans_le fit⟩

private theorem mem_block {N start len : ℕ} (fit : start + len ≤ N) (i : Fin N) :
    i ∈ block start len fit ↔ start ≤ i.val ∧ i.val < start + len := by
  rw [block, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩
    have := j.isLt
    change start ≤ start + j.val ∧ start + j.val < start + len
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨i.val - start, by omega⟩, Fin.ext (by simp; omega)⟩

/-- Physical offsets visited by the writer in ascending order. The first range
also contains the populated part of the left exterior field. -/
def cells (L : Lengths) (labels : ℕ) : List (Fin (span L labels)) :=
  block 0 (exteriorBase L + L.leftCut) (by
    have := L.leftFit; unfold exteriorBase span Header.count; omega) ++
  block (exteriorBase L + L.cutCapacity) L.rightCut (by
    have := L.rightFit; unfold exteriorBase span Header.count; omega) ++
  block (Header.count L) labels (by rfl)

/-- The write count uses the actual cut lengths, including at an empty endpoint. -/
theorem cells_length (L : Lengths) (labels : ℕ) :
    (cells L labels).length = exteriorBase L + L.leftCut + L.rightCut + labels := by
  simp [cells, block, Nat.add_assoc]

theorem mem_cells (L : Lengths) (labels : ℕ) (i : Fin (span L labels)) :
    i ∈ cells L labels ↔ i.val < exteriorBase L + L.leftCut ∨
      (exteriorBase L + L.cutCapacity ≤ i.val ∧
       i.val < exteriorBase L + L.cutCapacity + L.rightCut) ∨ Header.count L ≤ i.val := by
  have hi : i.val < Header.count L + labels := i.isLt
  simp only [cells, List.mem_append, mem_block]
  rw [mem_block (start := Header.count L) (len := labels) (N := span L labels) (by rfl) i]
  omega

theorem headerMemory_padding (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w))
    (i : Fin (span L hist.length)) (hi : i ∉ cells L hist.length) :
    headerMemory L hdr hist i.val = 0 := by
  rw [mem_cells] at hi
  simp only [exteriorBase] at hi
  unfold headerMemory
  dsimp only
  split_ifs <;> first | rfl | omega

theorem headerMemory_past_end (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w))
    {i : ℕ} (hi : span L hist.length ≤ i) : headerMemory L hdr hist i = 0 := by
  unfold span at hi
  rw [show i = Header.count L + (i - Header.count L) by omega, headerMemory_hist,
    List.getElem?_eq_none (by omega)]
  rfl

/-- Sparse writes into the live machine's separate area for the pair's headers. -/
def install (base : ℕ) (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w))
    (fit : base + span L hist.length ≤ 2 ^ w) (m : Memory w) : Memory w :=
  store (scratchAddress base fit) (fun i ↦ headerMemory L hdr hist i.val) (cells L hist.length) m

/-- All writes fall within the reserved prefix. In particular, separate live
scratch addresses may already hold data. -/
theorem install_outside (base : ℕ) (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w))
    (fit : base + span L hist.length ≤ 2 ^ w) (m : Memory w) (a : ℕ)
    (ha : a < base ∨ base + span L hist.length ≤ a) :
    install base L hdr hist fit m a = m a := by
  apply store_outside
  intro i _h
  have := i.isLt
  change a ≠ base + i.val
  omega

/-- Reading a translated virtual address in a zero-initialized header area
recovers the prescribed word. This includes all padding and unused sites. -/
theorem install_read (base : ℕ) (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w))
    (fit : base + span L hist.length ≤ 2 ^ w) (m : Memory w) (a : ℕ)
    (hz : m (base + a) = 0) :
    install base L hdr hist fit m (base + a) = headerMemory L hdr hist a := by
  by_cases h : a < span L hist.length
  · let i : Fin (span L hist.length) := ⟨a, h⟩
    by_cases hi : i ∈ cells L hist.length
    · exact store_at (scratchAddress base fit) (fun j ↦ headerMemory L hdr hist j.val) _ m hi
    · change install base L hdr hist fit m (base + a) = headerMemory L hdr hist i.val
      rw [headerMemory_padding _ _ _ _ hi, ← hz]
      apply store_outside
      intro j hj he
      have hij : i = j := Fin.ext (Nat.add_left_cancel he)
      exact hi (hij ▸ hj)
  · rw [headerMemory_past_end _ _ _ (Nat.le_of_not_gt h),
      install_outside _ _ _ _ _ _ _ (Or.inr (by omega)), hz]

open BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

/-- Copy a full computed word at offset `state - pub 0` between the arrays
at `pub 1` and `pub 2`. Used for cut lengths and histogram components. -/
def copyWord : List (Op 8 3) :=
  [.stateWord 0, .publicWord 1 0, .binary .sub 2 0 1, .publicWord 3 1, .binary .add 3 3 2,
   .read 4 3, .publicWord 5 2, .binary .add 5 5 2, .write 5 4, .constant 6 1, .binary .add 7 0 6]

/-- Each native word-copy call performs one read and one write and advances the
persistent cursor without branching. -/
theorem copyWord_native (pub : Fin 3 → Word w) (state : Word w) (m : Memory w) :
    let offset := state - pub 0
    let src := pub 1 + offset
    let dst := pub 2 + offset
    let machine := (template copyWord 7).instantiate w pub
    ∃ es, execute machine.program 12 (machine.program.start state) m [] =
        some ⟨es, some (state + 1)⟩ ∧
      after m es = writeMemory m dst (m src.val) ∧ es.length = 11 ∧
      countProbes es = 2 ∧ choiceBits es = [] := by
  dsimp only
  let src := pub 1 + (state - pub 0)
  let dst := pub 2 + (state - pub 0)
  let es : List (Event w) := [.tick, .tick, .tick, .tick, .tick, .read src (m src.val),
    .tick, .tick, .write dst (m src.val), .tick, .tick]
  refine ⟨es, ?_, rfl, rfl, rfl, rfl⟩
  change execute ((template copyWord 7).instantiate w pub).program (1 + copyWord.length)
    ⟨_, state, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  simp (config := { decide := true }) [copyWord, trace, Op.effect, Function.update, es, src, dst,
    show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl,
    show BinaryOp.sub.eval = (· - · : Word w → Word w → Word w) from rfl]

end LiveAuxiliaryHeaders

end VPVNP
end Computability
end OAI
