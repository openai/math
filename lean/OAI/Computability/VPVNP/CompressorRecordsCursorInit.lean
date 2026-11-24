import OAI.Computability.VPVNP.CompressorRecordsCursor

/-!
# Installing the scheduler row for the cursor incidence scan

The initializer reads eight public words. It multiplies the degree, cursor
count and two binary radices to obtain the loop count. Successive additions
give the starts of the six incidence columns. A single burst then writes the
worker tag, first row, row count and the worker's eleven parameters.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CursorRAM.ScheduleInit

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Row address, worker tag, degree, cursor count, low radix, lane radix,
arc width and first column address, in that order. -/
def inputs (row tag : Word w) (b l a W start : ℕ) : Fin 8 → Word w :=
  ![row, tag, encode w (2^a), encode w (b+l), encode w (2^b), encode w (2^l),
    encode w W, encode w start]

/-- Registers zero through seven cache the public inputs. Register eight holds
the row count, and nine through thirteen hold the remaining column starts. -/
private def setup : List (Op 17 8) :=
  [.publicWord 0 0, .publicWord 1 1, .publicWord 2 2, .publicWord 3 3,
   .publicWord 4 4, .publicWord 5 5, .publicWord 6 6, .publicWord 7 7,
   .binary .mul 8 3 4, .binary .mul 8 8 5, .binary .mul 8 8 2,
   .binary .add 9 7 8, .binary .add 10 9 8, .binary .add 11 10 8,
   .binary .add 12 11 8, .binary .add 13 12 8, .constant 14 0, .constant 15 1,
   .stateWord 16, .binary .add 16 16 15]

private def emit (r : Fin 17) : List (Op 17 8) := [.write 0 r, .binary .add 0 0 15]

/-- Fixed instruction table for every width and every admissible cursor graph. -/
def ops : List (Op 17 8) :=
  setup ++ [1,14,8,2,3,4,5,6,7,9,10,11,12,13].flatMap emit

private def values (p : Fin 8 → Word w) : List (Word w) :=
  let n := p 3 * p 4 * p 5 * p 2
  let s := p 7
  [p 1, 0, n, p 2, p 3, p 4, p 5, p 6, s, s+n, s+n+n, s+n+n+n,
    s+n+n+n+n, s+n+n+n+n+n]

private def emitLog (row : Word w) : List (Word w) → List (Event w)
  | [] => []
  | x :: xs => .write row x :: .tick :: emitLog (row + 1) xs

/-- All probes are writes in increasing row-field order. -/
def events (p : Fin 8 → Word w) : List (Event w) :=
  List.replicate setup.length .tick ++ emitLog (p 0) (values p)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem native_trace (p : Fin 8 → Word w) (m : Memory w) (state : Word w) :
    ∃ rs m', trace p state ops (fun _ ↦ 0) m = some (events p, rs, m') ∧ rs 16 = state + 1 := by
  simp (config := {decide := true}) [ops, setup, emit, events, emitLog, values, trace, Op.effect,
    BinaryOp.eval, Function.update, List.replicate_succ]

theorem native (p : Fin 8 → Word w) (m : Memory w) (state : Word w) :
    let M := (template ops 16).instantiate w p
    execute M.program (1 + ops.length) (M.program.start state) m [] =
      some ⟨events p, some (state + 1)⟩ := by
  obtain ⟨rs, m', h, ret⟩ := native_trace p m state
  let M := (template ops 16).instantiate w p
  change execute M.program (1 + ops.length) ⟨M.entry, state, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _
  rw [execute_template, run_eq_trace, h]
  simp [ret]

theorem work (p : Fin 8 → Word w) :
    ops.length = 48 ∧ (events p).length = 48 ∧ countProbes (events p) = 14 ∧
      choiceBits (events p) = [] := ⟨rfl, rfl, rfl, rfl⟩

private theorem after_emit (m : Memory w) (row : Word w) (xs : List (Word w)) :
    after m (emitLog row xs) = Greedy.writeRow m row xs := by
  induction xs generalizing m row with
  | nil => rfl
  | cons x xs ih => exact ih (writeMemory m row x) (row+1)

private theorem after_events (p : Fin 8 → Word w) (m : Memory w) :
    after m (events p) = Greedy.writeRow m (p 0) (values p) := after_emit m _ _

private theorem values_eq (row tag : Word w) (b l a W start : ℕ) :
    values (inputs row tag b l a W start) =
      tag :: 0 :: encode w (rowCount b l a) :: List.ofFn (publicWords w b l a W start) := by
  simp [values, inputs, publicWords, encode, rowCount, Fin.ofNat_eq_cast]
  repeat' apply And.intro
  all_goals ring

private theorem stores_at {m : Memory w} (xs : List (Word w)) (row : Word w)
    (h : Greedy.Stores m row xs) (fit : row.val + xs.length ≤ 2^w) {i : ℕ} (hi : i < xs.length) :
    m (row.val + i) = xs[i] := by
  induction xs generalizing row i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => exact h.1
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      have room : row.val + 1 < 2^w := by simp only [List.length_cons] at fit; omega
      have inc : (row + 1).val = row.val + 1 := by
        rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2^w), Nat.mod_eq_of_lt room]
      have ht := ih (row+1) h.2 (by rw [inc]; simp only [List.length_cons] at fit; omega) hi'
      simpa only [inc, Nat.add_right_comm, Nat.add_assoc, Nat.one_add, List.getElem_cons_succ] using ht

/-- From arbitrary external memory the compiled call installs the complete row
read by the scheduler. Fields three through thirteen agree with the parameters
of the cursor scan at the same degree, address split, width and array start. -/
theorem initialize_row (row tag state : Word w) (b l a W start : ℕ) (m : Memory w)
    (fit : row.val + 14 ≤ 2^w) :
    let p := inputs row tag b l a W start
    let M := (template ops 16).instantiate w p
    let out := after m (events p)
    execute M.program (1 + ops.length) (M.program.start state) m [] =
        some ⟨events p, some (state+1)⟩ ∧
      out row.val = tag ∧ out (row.val+1) = 0 ∧ out (row.val+2) = encode w (rowCount b l a) ∧
      (∀ i : Fin 11, out (row.val+3+i.val) = publicWords w b l a W start i) ∧
      (∀ addr, addr < row.val ∨ row.val + 14 ≤ addr → out addr = m addr) ∧
      (events p).length = 48 ∧ countProbes (events p) = 14 ∧ choiceBits (events p) = [] := by
  intro p M out
  let words := tag :: 0 :: encode w (rowCount b l a) :: List.ofFn (publicWords w b l a W start)
  have length : words.length = 14 := by simp [words]
  have mem : out = Greedy.writeRow m row words := by
    rw [show out = after m (events p) from rfl, after_events, values_eq]
    rfl
  have room : row.val + words.length ≤ 2^w := by rwa [length]
  have stored : Greedy.Stores out row words := mem ▸ Greedy.writeRow_stores m row words room
  have field (i : ℕ) (hi : i < words.length) := stores_at words row stored room hi
  refine ⟨native p m state, field (i := 0) (by omega), field (i := 1) (by omega),
    field (i := 2) (by omega), ?_, ?_, (work p).2⟩
  · intro i
    have hi := i.isLt
    have h := field (i := i.val+3) (by omega)
    rw [show row.val+3+i.val = row.val+(i.val+3) by omega]
    simpa only [words, List.getElem_cons_succ, List.getElem_ofFn] using h
  · intro addr ha
    exact mem ▸ Greedy.writeRow_outside m row words addr room (by rwa [length])

/-- The scheduler reads the exact natural exclusive bound when it fits in a word. -/
theorem stop_value (row tag : Word w) (b l a W start : ℕ) (m : Memory w)
    (room : row.val + 14 ≤ 2^w) (fit : rowCount b l a < 2^w) :
    let out := after m (events (inputs row tag b l a W start))
    (out (row.val+2)).val = rowCount b l a := by
  dsimp only
  rw [(initialize_row row tag 0 b l a W start m room).2.2.2.1]
  exact Nat.mod_eq_of_lt fit

end CompressorRecords.CursorRAM.ScheduleInit

end VPVNP
end Computability
end OAI
