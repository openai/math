import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.PrimedScheduleRAM
import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Defs

/-!
# Native prefix sums of sorted thick-wire widths

A persistent cursor visits each live width in row order. On the first visit
to a bundle the running total is reset, regardless of the previous memory
contents. The start of each wire and the final total of each bundle are
written to separate descriptor tables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundlePrefixRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Public words give the live row size, physical row stride, sorted-width
base, wire-start base, and row-total base. -/
def visit : List (Op 8 5) :=
  [.stateWord 0, .publicWord 1 0, .binary .div 2 0 1, .binary .mod 3 0 1,
   .publicWord 4 1, .binary .mul 4 2 4, .binary .add 4 4 3,
   .publicWord 5 2, .binary .add 5 5 4, .read 5 5,
   .publicWord 6 4, .binary .add 6 6 2, .read 7 6,
   .constant 1 1, .binary .add 3 3 1, .binary .div 3 1 3, .binary .sub 3 1 3,
   .binary .mul 7 3 7, .publicWord 3 3, .binary .add 3 3 4, .write 3 7,
   .binary .add 7 7 5, .write 6 7, .binary .add 0 0 1]

/-- The bundle row visited by a linear prefix-scan cursor. -/
def row (p : Fin 5 → Word w) (i : Word w) : Word w := BinaryOp.div.eval i (p 0)
/-- The cursor's position among the live items of its current bundle row. -/
def pos (p : Fin 5 → Word w) (i : Word w) : Word w := BinaryOp.mod.eval i (p 0)
/-- The item's offset in a strided rectangle, computed from its row number and live position. -/
def index (p : Fin 5 → Word w) (i : Word w) : Word w := row p i * p 1 + pos p i
/-- The word multiplier that discards the previous total at position zero and retains it at
later positions of a live row. -/
def gate (j : Word w) : Word w := 1 - BinaryOp.div.eval 1 (j + 1)
/-- The prefix offset for the current item, starting a fresh sum at the first item in each
bundle. -/
def start (p : Fin 5 → Word w) (mem : Memory w) (i : Word w) : Word w :=
  gate (pos p i) * mem (p 4 + row p i).val
/-- Read the current item's width from the strided input rectangle. -/
def width (p : Fin 5 → Word w) (mem : Memory w) (i : Word w) : Word w :=
  mem (p 2 + index p i).val

/-- Store the current item's prefix offset and advance its bundle's total by the item's width. -/
def stepMemory (p : Fin 5 → Word w) (mem : Memory w) (i : Word w) : Memory w :=
  writeMemory (writeMemory mem (p 3 + index p i) (start p mem i))
    (p 4 + row p i) (start p mem i + width p mem i)

/-- One prefix-scan visit's ticks and probes, reading the width and old row total before
writing the item start and updated total. -/
def events (p : Fin 5 → Word w) (mem : Memory w) (i : Word w) : List (Event w) :=
  let total := p 4 + row p i
  List.replicate 9 .tick ++ [.read (p 2 + index p i) (width p mem i), .tick, .tick,
    .read total (mem total.val)] ++ List.replicate 7 .tick ++
    [.write (p 3 + index p i) (start p mem i), .tick,
     .write total (start p mem i + width p mem i), .tick]

theorem native (p : Fin 5 → Word w) (mem : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 25 (M.program.start i) mem [] = some ⟨events p mem i, some (i + 1)⟩ := by
  let M := (template visit 0).instantiate w p
  change execute M.program (1 + visit.length) ⟨M.entry, i, fun _ => 0, fun _ => 0⟩ mem [] = _
  rw [execute_template, run_eq_trace]
  rfl

theorem events_after (p : Fin 5 → Word w) (mem : Memory w) (i : Word w) :
    after mem (events p mem i) = stepMemory p mem i := rfl

theorem events_work (p : Fin 5 → Word w) (mem : Memory w) (i : Word w) :
    countProbes (events p mem i) = 4 ∧ (events p mem i).length = 24 := ⟨rfl, rfl⟩

/-- Natural prefix sum in row `b` of the sorted-width table. -/
def prefixSum (p : Fin 5 → Word w) (initial : Memory w) (b j : ℕ) : ℕ :=
  ∑ a ∈ Finset.range j, (initial ((p 2).val + b * (p 1).val + a)).val

/-- The three physical regions fit, and each pair is disjoint in either order. -/
structure Layout (p : Fin 5 → Word w) (B : ℕ) : Prop where
  positive : 0 < (p 0).val
  size_le_stride : (p 0).val ≤ (p 1).val
  widthsFit : (p 2).val + B * (p 1).val ≤ 2 ^ w
  startsFit : (p 3).val + B * (p 1).val ≤ 2 ^ w
  totalsFit : (p 4).val + B ≤ 2 ^ w
  widthsStarts : (p 2).val + B * (p 1).val ≤ (p 3).val ∨ (p 3).val + B * (p 1).val ≤ (p 2).val
  widthsTotals : (p 2).val + B * (p 1).val ≤ (p 4).val ∨ (p 4).val + B ≤ (p 2).val
  startsTotals : (p 3).val + B * (p 1).val ≤ (p 4).val ∨ (p 4).val + B ≤ (p 3).val

theorem prefix_succ (p : Fin 5 → Word w) (m : Memory w) (b j : ℕ) :
    prefixSum p m b (j + 1) = prefixSum p m b j + (m ((p 2).val + b * (p 1).val + j)).val :=
  Finset.sum_range_succ ..

private theorem prefix_mono (p : Fin 5 → Word w) (m : Memory w) (b : ℕ) :
    Monotone (prefixSum p m b) := monotone_nat_of_le_succ fun j => by rw [prefix_succ]; omega

private theorem gate_exact (j : Word w) (hj : j.val + 1 < 2 ^ w) :
    gate j = if j.val = 0 then 0 else 1 := by
  have one : (1 : Word w).val = 1 := by
    change 1 % (2 ^ w) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have inc : (j + 1).val = j.val + 1 := by rw [Fin.val_add, one, Nat.mod_eq_of_lt hj]
  have div : (BinaryOp.div.eval (1 : Word w) (j + 1)).val = 1 / (j.val + 1) := by
    change (1 : Word w).val / (j + 1).val % (2 ^ w) = _
    rw [one, inc, Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt (by omega))]
  by_cases h : j.val = 0
  · have d : BinaryOp.div.eval (1 : Word w) (j + 1) = 1 := by
      apply Fin.ext
      rw [div, h, one]
    simp [gate, h, d]
  · have d : BinaryOp.div.eval (1 : Word w) (j + 1) = 0 := by
      apply Fin.ext
      rw [div, Nat.div_eq_of_lt (by omega)]
      rfl
    simp [gate, h, d]

private theorem coord_bound {B k stride b j : ℕ} (hb : b < B) (hj : j < k) (hs : k ≤ stride) :
    b * stride + j < B * stride := by
  have h := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hb)
  rw [Nat.succ_mul] at h
  omega

private theorem coord_unique {s b a j l : ℕ} (hj : j < s) (hl : l < s)
    (h : b * s + j = a * s + l) : b = a ∧ j = l := by
  have js := Nat.mul_add_mod_of_lt hj (a := b)
  have ls := Nat.mul_add_mod_of_lt hl (a := a)
  have eq : j = l := js.symm.trans ((congrArg (· % s) h).trans ls)
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel (eq ▸ h)), eq⟩

/-- The starts of all visited wires, and the latest nonempty prefix total
of each visited bundle, are stored. Every cell outside the writable rows
and the total column retains its initial value. -/
structure Saved (p : Fin 5 → Word w) (B t : ℕ) (initial mem : Memory w) : Prop where
  starts : ∀ b < B, ∀ j < (p 0).val, b * (p 0).val + j < t →
    (mem ((p 3).val + b * (p 1).val + j)).val = prefixSum p initial b j
  totals : ∀ b < B, ∀ q, 0 < q → q ≤ (p 0).val → b * (p 0).val + q ≤ t →
    (q = (p 0).val ∨ b * (p 0).val + q = t) →
    (mem ((p 4).val + b)).val = prefixSum p initial b q
  frame : ∀ addr,
    (∀ b < B, ∀ j < (p 0).val, addr ≠ (p 3).val + b * (p 1).val + j) →
    (∀ b < B, addr ≠ (p 4).val + b) → mem addr = initial addr


private theorem starts_ne_total {p : Fin 5 → Word w} {B b j u : ℕ}
    (layout : Layout p B) (hb : b < B) (hj : j < (p 0).val) (hu : u < B) :
    (p 3).val + b * (p 1).val + j ≠ (p 4).val + u := by
  have h := coord_bound hb hj layout.size_le_stride
  have dis := layout.startsTotals
  omega

theorem Saved.widths {p : Fin 5 → Word w} {B t : ℕ} {initial mem : Memory w}
    (done : Saved p B t initial mem) (layout : Layout p B) (b j : ℕ)
    (hb : b < B) (hj : j < (p 0).val) :
    mem ((p 2).val + b * (p 1).val + j) = initial ((p 2).val + b * (p 1).val + j) := by
  have h := coord_bound hb hj layout.size_le_stride
  apply done.frame
  · intro a ha l hl
    have bound := coord_bound ha hl layout.size_le_stride
    have apart := layout.widthsStarts
    omega
  · intro a ha
    have apart := layout.widthsTotals
    omega

private theorem saved_step {p : Fin 5 → Word w} {B t : ℕ} {initial mem : Memory w}
    (layout : Layout p B) (fit : ∀ b < B, prefixSum p initial b (p 0).val < 2^w)
    (done : Saved p B t initial mem) (i : Word w) (hi : i.val = t)
    (ht : t < B * (p 0).val) :
    Saved p B (t+1) initial (stepMemory p mem i) := by
  let b := t / (p 0).val
  let j := t % (p 0).val
  have hb : b < B := (Nat.div_lt_iff_lt_mul layout.positive).mpr ht
  have hj : j < (p 0).val := Nat.mod_lt _ layout.positive
  have ht' : t = b * (p 0).val + j := by
    dsimp [b, j]
    rw [Nat.mul_comm, Nat.div_add_mod]
  have hr : (row p i).val = b := by
    change (i.val / (p 0).val) % (2 ^ w) = _
    rw [Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt i.isLt), hi]
  have hp : (pos p i).val = j := by
    change (i.val % (p 0).val) % (2 ^ w) = _
    rw [Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt i.isLt), hi]
  have offBound := coord_bound hb hj layout.size_le_stride
  have wf := layout.widthsFit
  have sf := layout.startsFit
  have tf := layout.totalsFit
  have off : (index p i).val = b * (p 1).val + j := by
    rw [index, Fin.val_add, Fin.val_mul, hr, hp, Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega)]
  have wa : (p 2 + index p i).val = (p 2).val + b * (p 1).val + j := by
    rw [Fin.val_add, off, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
  have sa : (p 3 + index p i).val = (p 3).val + b * (p 1).val + j := by
    rw [Fin.val_add, off, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
  have ta : (p 4 + row p i).val = (p 4).val + b := by
    rw [Fin.val_add, hr, Nat.mod_eq_of_lt (by omega)]
  have wval : width p mem i = initial ((p 2).val + b * (p 1).val + j) := by
    rw [width, wa, done.widths layout b j hb hj]
  have sval : (start p mem i).val = prefixSum p initial b j := by
    have kg := (p 0).isLt
    rw [start, gate_exact _ (by rw [hp]; omega), hp, ta]
    by_cases hzero : j = 0
    · simp [hzero, prefixSum]
    · rw [ite_eq_right hzero, one_mul]
      exact done.totals b hb j (by omega) hj.le (by omega) (.inr ht'.symm)
  have totalFit : prefixSum p initial b (j+1) < 2^w :=
    ((prefix_mono p initial b) (Nat.succ_le_of_lt hj)).trans_lt (fit b hb)
  have tval : (start p mem i + width p mem i).val = prefixSum p initial b (j+1) := by
    rw [Fin.val_add, sval, wval, ← prefix_succ, Nat.mod_eq_of_lt totalFit]
  constructor
  · intro a ha l hl hvisit
    have diff := starts_ne_total layout ha hl hb
    simp only [stepMemory, writeMemory, ta, sa, ite_eq_right diff]
    by_cases eq : (p 3).val + a * (p 1).val + l = (p 3).val + b * (p 1).val + j
    · obtain ⟨rfl, rfl⟩ := coord_unique (hl.trans_le layout.size_le_stride)
        (hj.trans_le layout.size_le_stride) (by omega : a * (p 1).val + l = b * (p 1).val + j)
      rw [ite_eq_left rfl]
      exact sval
    · rw [ite_eq_right eq]
      have hn : a * (p 0).val + l ≠ t := by
        intro same
        obtain ⟨rfl,rfl⟩ := coord_unique hl hj (same.trans ht')
        exact eq rfl
      exact done.starts a ha l hl (by omega)
  · intro a ha q hq hqk hvisit latest
    have diff := Ne.symm (starts_ne_total layout hb hj ha)
    simp only [stepMemory, writeMemory, ta, sa, ite_eq_right diff]
    by_cases same : a = b
    · subst a
      have eq : q = j+1 := by rcases latest with h | h <;> omega
      rw [ite_eq_left rfl, eq]
      exact tval
    · rw [ite_eq_right (fun h => same (Nat.add_left_cancel h))]
      have before : a * (p 0).val + q ≠ t + 1 := by
        intro eq
        have e : a * (p 0).val + (q-1) = b * (p 0).val + j := by omega
        exact same (coord_unique (by omega) hj e).1
      exact done.totals a ha q hq hqk (by omega) (.inl (latest.resolve_right before))
  · intro addr hs ht
    simp only [stepMemory, writeMemory, ta, sa, ite_eq_right (hs b hb j hj),
      ite_eq_right (ht b hb), done.frame addr hs ht]

/-- Execution and work of a prefix of the native calls. -/
structure ScanRun (p : Fin 5 → Word w) (B t : ℕ) (initial : Memory w) (rs : List (Report w)) : Prop where
  executed : runSegment ((template visit 0).instantiate w p).program 25 (some 0)
    initial (List.replicate t []) = some rs
  cursor : endState (some 0) rs = some (Fin.ofNat _ t)
  saved : Saved p B t initial (after initial (eventLog rs))
  length : rs.length = t
  work : ∀ r ∈ rs, r.probes = 4 ∧ r.events.length = 24
  cost : RAMBuckets.cost Report.probes rs = 5 * t

theorem scan_run (p : Fin 5 → Word w) (B : ℕ) (initial : Memory w) (layout : Layout p B)
    (fit : ∀ b < B, prefixSum p initial b (p 0).val < 2^w)
    (t : ℕ) (ht : t ≤ B * (p 0).val) : ∃ rs, ScanRun p B t initial rs := by
  induction t with
  | zero =>
    refine ⟨[], rfl, rfl, ⟨?_, ?_, fun _ _ _ => rfl⟩, rfl, by simp, rfl⟩ <;> intros <;> omega
  | succ t ih =>
    obtain ⟨rs, prev⟩ := ih (by omega)
    let i := Fin.ofNat (2 ^ w) t
    let mem := after initial (eventLog rs)
    let r : Report w := ⟨events p mem i, some (i + 1)⟩
    have hbound := Nat.mul_le_mul_left B layout.size_le_stride
    have hw := layout.widthsFit
    have hv : i.val = t := Nat.mod_eq_of_lt (by omega)
    have inc : i+1 = Fin.ofNat (2 ^ w) (t+1) := by
      apply Fin.ext
      simp [i, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]
    have afterBoth : after initial (eventLog (rs ++ [r])) = stepMemory p mem i := by
      simp only [eventLog, List.flatMap_append, List.flatMap_singleton, after, List.foldl_append, mem]
      rfl
    refine ⟨rs ++ [r], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.replicate_succ', PrimedSchedule.runSegment_append, prev.executed]
      simp only [Option.bind_some, prev.cursor, runSegment, Option.map_some]
      change (match execute ((template visit 0).instantiate w p).program 25
          (((template visit 0).instantiate w p).program.start i) mem [] with
        | none => none | some s => some [s]).map (rs ++ ·) = _
      rw [native p mem i]
      rfl
    · rw [endState_append, prev.cursor]
      exact congrArg some inc
    · rw [afterBoth]
      exact saved_step layout fit prev.saved i hv ht
    · simp [prev.length]
    · intro s hs
      rcases List.mem_append.mp hs with he | he
      · exact prev.work s he
      · obtain rfl := List.mem_singleton.mp he
        exact events_work p mem i
    · have hp : r.probes = 4 := (events_work p mem i).1
      rw [RAMBuckets.cost_append, prev.cost, RAMBuckets.cost, hp, RAMBuckets.cost, Nat.mul_succ]

/-- Full row-major execution, including exact natural wire offsets and row
totals. The frame includes the padding cells between live row prefixes. -/
structure FullRun (p : Fin 5 → Word w) (B : ℕ) (initial : Memory w) (rs : List (Report w)) : Prop
    extends ScanRun p B (B * (p 0).val) initial rs where
  starts : ∀ b < B, ∀ j < (p 0).val, (after initial (eventLog rs) ((p 3).val + b * (p 1).val + j)).val =
    prefixSum p initial b j
  totals : ∀ b < B, (after initial (eventLog rs) ((p 4).val + b)).val = prefixSum p initial b (p 0).val
  frame : ∀ addr,
    (∀ b < B, ∀ j < (p 0).val, addr ≠ (p 3).val + b * (p 1).val + j) →
    (∀ b < B, addr ≠ (p 4).val + b) → after initial (eventLog rs) addr = initial addr

/-- A single fixed program scans all `B*k` entries. Only input width sums
must fit in a word. Every row total is initialized by the worker itself. -/
theorem full_run (p : Fin 5 → Word w) (B : ℕ) (initial : Memory w) (layout : Layout p B)
    (fit : ∀ b < B, prefixSum p initial b (p 0).val < 2^w) :
    ∃ rs, FullRun p B initial rs := by
  obtain ⟨rs, run⟩ := scan_run p B initial layout fit (B * (p 0).val) (le_refl _)
  refine ⟨rs, run, ?_, ?_, run.saved.frame⟩
  · intro b hb j hj
    exact run.saved.starts b hb j hj (coord_bound hb hj (le_refl _))
  · intro b hb
    have bound := Nat.mul_le_mul_right (p 0).val (Nat.succ_le_of_lt hb)
    rw [Nat.succ_mul] at bound
    exact run.saved.totals b hb (p 0).val layout.positive (le_refl _) bound (.inl rfl)

end CompressorRecords.BundlePrefixRAM

end VPVNP
end Computability
end OAI
