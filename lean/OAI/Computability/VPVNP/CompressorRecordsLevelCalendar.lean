import OAI.Computability.VPVNP.CompressorRecordsSchedule

/-!
# Online controller for repeated descriptor phases

The finite controller contains the planner tags for an initial sequence and
for one compression block. On each entry it reads the current ordinal and
the total number of phases. A quotient and remainder recover the current
block and its phase. The controller writes the planner tag and returns the address of the
current block header. The subsequent row launch increments the ordinal.
At the total it accepts. The same finite instruction table serves every block count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.LevelCalendar

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w d : ℕ}

/-- The initial and repeated tags are operands in the program text. -/
structure Calendar (d : ℕ) where
  /-- Planner tags visited once before the first repeated compression block. -/
  initial : List (Fin d)
  /-- Planner tags traversed in order for each repetition of a compression block. -/
  block : List (Fin d)
  /-- Words reserved per directory row when locating the level headers after the directory. -/
  rowPitch : ℕ
  /-- Number of level-header strides from the start of one compression block to the next. -/
  levelsPerBlock : ℕ

/-- Number of distinct phase slots in the initial sequence and one copy of the repeated block. -/
def Calendar.size (A : Calendar d) := A.initial.length + A.block.length
/-- Number of scheduled phases for the given block count, including the initial phases exactly
once. -/
def Calendar.total (A : Calendar d) (blocks : ℕ) := A.initial.length + blocks*A.block.length
/-- Convert a chronological ordinal to a finite phase slot, using the remainder within the
repeated block after the initial sequence. -/
def Calendar.phase (A : Calendar d) (j : ℕ) :=
  if j < A.initial.length then j else A.initial.length + (j-A.initial.length)%A.block.length
/-- The zero-based block number containing a repeated phase, with initial phases assigned to
block zero. -/
def Calendar.level (A : Calendar d) (j : ℕ) :=
  if j < A.initial.length then 0 else (j-A.initial.length)/A.block.length

theorem Calendar.phase_lt (A : Calendar d) {j blocks : ℕ} (h : j < A.total blocks) :
    A.phase j < A.size := by
  unfold Calendar.phase Calendar.size
  split_ifs with hj
  · omega
  · have hn : 0 < A.block.length := by
      by_contra! he
      have hzero : A.block.length = 0 := by omega
      simp [Calendar.total, hzero] at h
      omega
    exact Nat.add_lt_add_left (Nat.mod_lt _ hn) _

theorem Calendar.block_phase (A : Calendar d) (t : ℕ) (i : Fin A.block.length) :
    A.phase (A.initial.length + t*A.block.length+i.val) = A.initial.length+i.val ∧
    A.level (A.initial.length + t*A.block.length+i.val) = t := by
  have hi := i.isLt
  simp only [Calendar.phase, Calendar.level, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.mul_add_mod_of_lt hi]
  simp only [show ¬ A.initial.length+(t*A.block.length+i.val) < A.initial.length by omega, ↓reduceIte]
  rw [Nat.mul_comm t, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]
  trivial

theorem Calendar.level_lt (A : Calendar d) {j blocks : ℕ} (h : j < A.total blocks)
    (hblock : A.initial.length ≤ j) : A.level j < blocks := by
  have hn : 0 < A.block.length := by
    by_contra! he
    simp [Calendar.total, show A.block.length = 0 by omega] at h
    omega
  rw [Calendar.level, ite_eq_right (not_lt.mpr hblock), Nat.div_lt_iff_lt_mul hn]
  unfold Calendar.total at h
  omega

/-- The planner tag at a phase slot in the concatenation of the initial sequence and one
repeated block. -/
def Calendar.planner (A : Calendar d) (i : Fin A.size) : Fin d :=
  (A.initial ++ A.block)[i.val]'(by simpa [Calendar.size] using i.isLt)

/-- Number of native calendar instruction labels, with 31 shared rows and three lookup rows per
phase slot. -/
abbrev PCs (A : Calendar d) := 31 + A.size*3
private def labels (A : Calendar d) : Fin 31 ⊕ (Fin A.size × Fin 3) ≃ Fin (PCs A) :=
  ((Equiv.refl _).sumCongr finProdFinEquiv).trans finSumFinEquiv
private def head (A : Calendar d) (i : Fin 31) := labels A (.inl i)
private def slot (A : Calendar d) (i : Fin A.size) (q : Fin 3) := labels A (.inr (i,q))
private def lookup (A : Calendar d) (n : ℕ) :=
  if h : n < A.size then slot A ⟨n,h⟩ 0 else head A 25

/-- Enough bits to represent the tags, phase indices, row pitch and number
of levels per block. The level size is read from RAM. -/
def literalWidth (A : Calendar d) := Nat.clog 2 (A.size+d+A.rowPitch+A.levelsPerBlock+2)
private def lit (A : Calendar d) (n : ℕ) : Word (literalWidth A) := Fin.ofNat _ n

private def headCode (A : Calendar d) : Fin 31 → Instr (literalWidth A) (PCs A) 11 5
  | 0 => .publicWord 0 2 (head A 1)
  | 1 => .readExternal 1 0 (head A 2)
  | 2 => .publicWord 2 3 (head A 3)
  | 3 => .readExternal 2 2 (head A 4)
  | 4 => .jumpLt 1 2 (head A 5) (head A 24)
  | 5 => .constant 3 (lit A A.initial.length) (head A 6)
  | 6 => .jumpLt 1 3 (head A 7) (head A 9)
  | 7 => .copy 4 1 (head A 8)
  | 8 => .constant 5 (lit A 0) (head A 14)
  | 9 => .binary .sub 6 1 3 (head A 10)
  | 10 => .constant 7 (lit A A.block.length) (head A 11)
  | 11 => .binary .div 5 6 7 (head A 12)
  | 12 => .binary .mod 4 6 7 (head A 13)
  | 13 => .binary .add 4 3 4 (head A 14)
  | 14 => .publicWord 8 1 (head A 15)
  | 15 => .constant 9 (lit A A.rowPitch) (head A 16)
  | 16 => .binary .mul 9 9 2 (head A 17)
  | 17 => .binary .add 8 8 9 (head A 18)
  | 18 => .publicWord 9 1 (head A 26)
  | 19 => .binary .mul 9 9 5 (head A 20)
  | 20 => .binary .add 8 8 9 (head A 21)
  | 21 => .publicWord 7 4 (lookup A 0)
  | 22 => .writeExternal 7 10 (head A 23)
  | 23 => .returnState 8
  | 24 => .accept
  | 25 => .reject
  | 26 => .constant 10 (lit A 1) (head A 27)
  | 27 => .binary .sub 9 9 10 (head A 28)
  | 28 => .readExternal 9 9 (head A 29)
  | 29 => .constant 10 (lit A A.levelsPerBlock) (head A 30)
  | _ => .binary .mul 9 9 10 (head A 19)

private def slotCode (A : Calendar d) (i : Fin A.size) : Fin 3 → Instr (literalWidth A) (PCs A) 11 5
  | 0 => .constant 10 (lit A i.val) (slot A i 1)
  | 1 => .jumpEq 4 10 (slot A i 2) (lookup A (i.val+1))
  | 2 => .constant 10 (lit A (A.planner i).succ.val) (head A 22)

/-- Finite instruction table that reads the current ordinal, locates its block header and
dispatches its planner, or accepts at the schedule end. -/
def table (A : Calendar d) : Template (PCs A) 11 5 where
  literalWidth := literalWidth A
  entry := head A 0
  code pc := match (labels A).symm pc with
    | .inl i => headCode A i
    | .inr (i,q) => slotCode A i q

/-- Instantiate the level calendar's instruction table at the chosen word width and five public
operands. -/
abbrev machine (A : Calendar d) (pub : Fin 5 → Word w) := (table A).instantiate w pub

private theorem code_head (A : Calendar d) (pub : Fin 5 → Word w) (i : Fin 31) :
    (machine A pub).code (head A i) = (headCode A i).resize w := by
  simp [machine, table, Template.instantiate, head]
private theorem code_slot (A : Calendar d) (pub : Fin 5 → Word w) (i : Fin A.size) (q : Fin 3) :
    (machine A pub).code (slot A i q) = (slotCode A i q).resize w := by
  simp [machine, table, Template.instantiate, slot]

private theorem lit_val (A : Calendar d) (n : ℕ) (hn : n < A.size+d+A.rowPitch+A.levelsPerBlock+2) :
    (lit A n).val = n := Nat.mod_eq_of_lt (hn.trans_le (Nat.le_pow_clog (by decide) _))

private theorem step (A : Calendar d) (pub : Fin 5 → Word w) (pc : Fin (PCs A)) (s : Word w)
    (rs : Fin 11 → Word w) (priv : Word w → Word w) :
    (machine A pub).program.step ⟨pc,s,rs,priv⟩ = ((machine A pub).code pc).run pub ⟨pc,s,rs,priv⟩ := rfl

private def boot (pub : Fin 5 → Word w) (m : Memory w) : List (Event w) :=
  [.tick,.read (pub 2) (m (pub 2).val),.tick,.read (pub 3) (m (pub 3).val),.tick]

/-- The accepting calendar report after reading the ordinal and total phase count, with no
continuation state. -/
def closedReport (pub : Fin 5 → Word w) (m : Memory w) : Report w := ⟨boot pub m,none⟩

private def lookedUp (A : Calendar d) (i : Fin A.size) (rs : Fin 11 → Word w) (n : ℕ) : Report w :=
  ⟨List.replicate (2*n+3) .tick ++ [.write (rs 7) (LiveStageLink.tagWord w (A.planner i).succ)],some (rs 8)⟩

private theorem scan (A : Calendar d) (pub : Fin 5 → Word w) (s : Word w)
    (m : Memory w) (bs : List Bool) (f : ℕ) (i : Fin A.size) (room : A.size ≤ 2^w)
    (rs : Fin 11 → Word w) (hr : rs 4 = (i.val : Word w)) (k n : ℕ) (hn : k+n = i.val) :
    execute (machine A pub).program (f+5+2*n) ⟨lookup A k,s,rs,fun _ ↦ 0⟩ m bs =
      if bs = [] then some (lookedUp A i rs n) else none := by
  induction n generalizing k rs with
  | zero =>
    have hk : k = i.val := by omega
    subst k
    rw [show lookup A i.val = slot A i 0 by simp [lookup,i.isLt]]
    have hidx := lit_val A i.val (by have := i.isLt; omega)
    have htag := lit_val A ((A.planner i).val+1) (by have := (A.planner i).isLt; omega)
    by_cases hb : bs = [] <;>
      simp (config := {decide := true}) [execute, step, code_slot, slotCode, code_head, headCode,
        Instr.resize, Instr.run, Config.put, hidx, htag, hr, hb, lookedUp,
        LiveStageLink.tagWord, Report.prepend]
  | succ n ih =>
    have hk : k < i.val := by omega
    let j : Fin A.size := ⟨k,hk.trans i.isLt⟩
    have he : lookup A k = slot A j 0 := by simp [lookup,j,j.isLt]
    have hne : (i.val : Word w) ≠ (k : Word w) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natCast, Nat.mod_eq_of_lt (hk.trans_le (i.isLt.trans_le room).le),
        Nat.mod_eq_of_lt (i.isLt.trans_le room)] at hv
      omega
    have hidx := lit_val A j.val (by have := j.isLt; omega)
    let rs' := Function.update rs (10 : Fin 11) (k : Word w)
    have hrest := ih rs' (by simpa [rs'] using hr) (k+1) (by omega)
    rw [show f+5+2*(n+1) = (f+5+2*n)+2 by omega, he]
    simp (config := {decide := true}) only [execute, step, code_slot, slotCode, Instr.resize,
      Instr.run, Config.put, hidx, Fin.ofNat_eq_cast, Function.update_self, Function.update_of_ne (show (4:Fin 11) ≠ 10 by decide),
      hr, hne, ↓reduceIte, j]
    rw [hrest]
    by_cases hb : bs = [] <;> simp (config := {decide := true}) [hb,lookedUp,rs',
      Report.prepend, show 2*(n+1)+3 = (2*n+3)+2 by omega, List.replicate_succ]

private def finishing (A : Calendar d) (pub : Fin 5 → Word w) (i : Fin A.size)
    (rs : Fin 11 → Word w) (m : Memory w) : Report w :=
  let gap := pub 1-1
  ⟨List.replicate 7 .tick ++ [.read gap (m gap.val)] ++
    List.replicate (2*i.val+3+5) .tick ++ [.write (pub 4) (LiveStageLink.tagWord w (A.planner i).succ)],
    some (pub 1 + (A.rowPitch : Word w)*rs 2 + (m gap.val*(A.levelsPerBlock : Word w))*rs 5)⟩

set_option maxRecDepth 8192 in
private theorem finish (A : Calendar d) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (f : ℕ) (i : Fin A.size) (room : A.size ≤ 2^w)
    (rs : Fin 11 → Word w) (hr : rs 4 = (i.val : Word w)) :
    execute (machine A pub).program ((f+5+2*i.val)+13) ⟨head A 14,s,rs,fun _ ↦ 0⟩ m bs =
      if bs = [] then some (finishing A pub i rs m) else none := by
  have hp := lit_val A A.levelsPerBlock (by omega)
  have hrow := lit_val A A.rowPitch (by omega)
  have hone := lit_val A 1 (by omega)
  simp (config := {decide := true}) [execute, step, code_head, headCode, Instr.resize, Instr.run,
    Config.put, hp, hrow, hone, BinaryOp.eval]
  rw [scan A pub s m bs f i room _ (by simpa using hr) 0 i.val (by omega)]
  by_cases hb : bs = [] <;> simp (config := {decide := true}) [hb,finishing,lookedUp,
    Report.prepend, Function.comp_def, List.replicate_succ]

/-- Level headers immediately follow the directory with one fixed-pitch row
per ordinal. The planner receives the address of the current header. -/
def header (A : Calendar d) (pub : Fin 5 → Word w) (m : Memory w) :=
  pub 1 + (A.rowPitch : Word w)*m (pub 3).val +
    (m (pub 1-1).val*(A.levelsPerBlock : Word w))*(A.level (m (pub 2).val).val : Word w)

/-- Planner tag and current header selected by the cursor calculation. -/
def dispatchReport (A : Calendar d) (pub : Fin 5 → Word w) (m : Memory w) (i : Fin A.size) : Report w :=
  let ord := m (pub 2).val
  let steps := if ord.val < A.initial.length then 4 else 7
  let gap := pub 1-1
  ⟨boot pub m ++ List.replicate (7+steps) .tick ++ [.read gap (m gap.val)] ++
    List.replicate (2*i.val+3+5) .tick ++
    [.write (pub 4) (LiveStageLink.tagWord w (A.planner i).succ)], some (header A pub m)⟩

private theorem atStart (A : Calendar d) (pub : Fin 5 → Word w) (s : Word w) :
    (machine A pub).program.start s = ⟨head A 0,s,fun _ ↦ 0,fun _ ↦ 0⟩ := rfl

/-- The capacity test consumes two reads and accepts at or beyond the
exclusive bound. Nonempty branch strings are rejected. -/
theorem execute_closed (A : Calendar d) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (closed : m (pub 3).val ≤ m (pub 2).val) {cap : ℕ} (hc : 6 ≤ cap) :
    execute (machine A pub).program cap ((machine A pub).program.start s) m bs =
      if bs = [] then some (closedReport pub m) else none := by
  obtain ⟨f,rfl⟩ : ∃ f, cap = f+6 := ⟨cap-6,by omega⟩
  rw [atStart]
  by_cases hb : bs = [] <;>
    simp (config := {decide := true}) [execute, step, code_head, headCode, Instr.resize, Instr.run,
      Config.put, not_lt_of_ge closed, hb, closedReport, boot, Report.prepend]

set_option maxRecDepth 8192 in
/-- The ordinal selects a planner from the finite program text. The bound, ordinal and level-stride
reads are followed by the planner tag write. The return word points
to the current header for the planner to read on the next call. -/
theorem execute_dispatch (A : Calendar d) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (active : m (pub 2).val < m (pub 3).val)
    (i : Fin A.size) (hi : A.phase (m (pub 2).val).val = i.val)
    (room : A.size < 2^w) {cap : ℕ} (hc : 30+2*A.size ≤ cap) :
    execute (machine A pub).program cap ((machine A pub).program.start s) m bs =
      if bs = [] then some (dispatchReport A pub m i) else none := by
  let ord := m (pub 2).val
  change A.phase ord.val = i.val at hi
  have hord : (ord.val : Word w) = ord := Fin.ext (Nat.mod_eq_of_lt ord.isLt)
  have hpre : A.initial.length < 2^w := by unfold Calendar.size at room; omega
  have hblock : A.block.length < 2^w := by unfold Calendar.size at room; omega
  have hp := lit_val A A.initial.length (by unfold Calendar.size; omega)
  have hb := lit_val A A.block.length (by unfold Calendar.size; omega)
  have hz := lit_val A 0 (by omega)
  have hcmp : ord < (A.initial.length : Word w) ↔ ord.val < A.initial.length := by
    change ord.val < A.initial.length % (2^w) ↔ _
    rw [Nat.mod_eq_of_lt hpre]
  rw [atStart]
  by_cases init : ord.val < A.initial.length
  · have hc' : 27+2*i.val ≤ cap := by have := i.isLt; omega
    obtain ⟨f,hf⟩ : ∃ f, cap = ((f+5+2*i.val)+13)+9 := ⟨cap-(27+2*i.val),by omega⟩
    have hw := hcmp.mpr init
    have hidx : ord = (i.val : Word w) := by
      have hx : ord.val = i.val := by simpa only [Calendar.phase, init, ↓reduceIte] using hi
      exact hord.symm.trans (congrArg (fun n : ℕ ↦ (n : Word w)) hx)
    rw [hf]
    generalize hfuel : (f+5+2*i.val)+13 = rest
    simp (config := {decide := true}) [execute, step, code_head, headCode, Instr.resize, Instr.run,
      Config.put, hp, hz, active, show m (pub 2).val < (A.initial.length : Word w) from hw]
    rw [← hfuel, finish A pub s m bs f i room.le _ (by simpa using hidx)]
    by_cases hs : bs = [] <;> simp (config := {decide := true}) [hs,dispatchReport,boot,finishing,
      header, Report.prepend, Function.comp_def, List.replicate_succ, Calendar.level,
      show (m (pub 2).val).val < A.initial.length from init]
  · have hc' : 30+2*i.val ≤ cap := by have := i.isLt; omega
    obtain ⟨f,hf⟩ : ∃ f, cap = ((f+5+2*i.val)+13)+12 := ⟨cap-(30+2*i.val),by omega⟩
    have hw := mt hcmp.mp init
    have hsub : (ord-(A.initial.length : Word w)).val = ord.val-A.initial.length := by
      have hx : ord - (A.initial.length : Word w) = ((ord.val-A.initial.length : ℕ) : Word w) := by
        rw [Nat.cast_sub (Nat.le_of_not_gt init), hord]
      rw [hx, Fin.val_natCast, Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt ord.isLt)]
    have hidx : (A.initial.length : Word w) + ((ord.val-A.initial.length)%A.block.length : ℕ) =
        (i.val : Word w) := by
      rw [← Nat.cast_add]
      exact congrArg (fun n : ℕ ↦ (n : Word w)) (by simpa only [Calendar.phase, init, ↓reduceIte] using hi)
    rw [hf]
    generalize hfuel : (f+5+2*i.val)+13 = rest
    simp (config := {decide := true}) [execute, step, code_head, headCode, Instr.resize, Instr.run,
      Config.put, hp, hb, active, show ¬m (pub 2).val < (A.initial.length : Word w) from hw, BinaryOp.eval]
    rw [← hfuel, finish A pub s m bs f i room.le _ (by
      simpa (config := {decide := true}) [show (m (pub 2).val-(A.initial.length : Word w)).val =
        (m (pub 2).val).val-A.initial.length from hsub, Nat.mod_eq_of_lt hblock] using hidx)]
    by_cases hs : bs = [] <;> simp (config := {decide := true}) [hs,dispatchReport,boot,finishing,
      header, Report.prepend, Function.comp_def, List.replicate_succ, Calendar.level,
      show ¬(m (pub 2).val).val < A.initial.length from init, show (m (pub 2).val-(A.initial.length : Word w)).val =
        (m (pub 2).val).val-A.initial.length from hsub, Nat.mod_eq_of_lt hblock]

theorem Calendar.planner_initial (A : Calendar d) (i : Fin A.initial.length) :
    A.planner (i.castAdd A.block.length) = A.initial[i.val] := by
  change (A.initial ++ A.block)[i.val]'(by simp; omega) = A.initial[i.val]
  rw [List.getElem_append_left i.isLt]

theorem Calendar.planner_block (A : Calendar d) (i : Fin A.block.length) :
    A.planner (i.natAdd A.initial.length) = A.block[i.val] := by
  unfold Calendar.planner
  rw [List.getElem_append_right (by simp)]
  simp

/-- Stage zero launches the row, the next stages are the data workers,
and the calendar follows them. The recipe tags follow the calendar in
initial-then-block order. -/
def recipeCalendar (workers initial phases rowPitch levelsPerBlock : ℕ) :
    Calendar (workers+1+(initial+phases)) where
  initial := List.ofFn fun i : Fin initial ↦ (i.castAdd phases).natAdd (workers+1)
  block := List.ofFn fun i : Fin phases ↦ (i.natAdd initial).natAdd (workers+1)
  rowPitch := rowPitch
  levelsPerBlock := levelsPerBlock

theorem recipe_tag (workers initial phases rowPitch levelsPerBlock : ℕ)
    (i : Fin (recipeCalendar workers initial phases rowPitch levelsPerBlock).size) :
    ((recipeCalendar workers initial phases rowPitch levelsPerBlock).planner i).succ.val = workers+2+i.val := by
  unfold Calendar.planner
  simp only [recipeCalendar, Fin.val_succ]
  by_cases h : i.val < initial
  · rw [List.getElem_append_left (by simpa using h)]
    simp
    omega
  · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt h)]
    simp
    omega

/-- For every block count and every active ordinal the phase index exists.
The read-only phase table has only one copy of the repeated block. -/
theorem execute_active (A : Calendar d) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (blocks : ℕ) (total : (m (pub 3).val).val = A.total blocks)
    (active : m (pub 2).val < m (pub 3).val)
    (room : A.size < 2^w) {cap : ℕ} (hc : 30+2*A.size ≤ cap) :
    let i : Fin A.size := ⟨A.phase (m (pub 2).val).val,A.phase_lt (total ▸ Fin.lt_def.mp active)⟩
    ∀ bs, execute (machine A pub).program cap ((machine A pub).program.start s) m bs =
      if bs = [] then some (dispatchReport A pub m i) else none := by
  intro i bs
  exact execute_dispatch A pub s m bs active i rfl room hc

private theorem ticks (m : Memory w) (n : ℕ) :
    after m (List.replicate n .tick) = m ∧ countProbes (List.replicate n (.tick : Event w)) = 0 ∧
    choiceBits (List.replicate n (.tick : Event w)) = [] := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih => simpa only [List.replicate_succ, after, List.foldl_cons, update, countProbes,
      choiceBits] using ih

private theorem ticks_write (n : ℕ) (a v : Word w) :
    countProbes (List.replicate n .tick ++ [.write a v]) = 1 ∧
      choiceBits (List.replicate n .tick ++ [.write a v]) = [] := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, countProbes, choiceBits] using ih

/-- The selected recipe sees the original ordinal and directory. There are
three reads, one tag write, and zero nondeterministic choices. -/
theorem dispatch_effect (A : Calendar d) (pub : Fin 5 → Word w) (m : Memory w) (i : Fin A.size) :
    let rep := dispatchReport A pub m i
    after m rep.events = writeMemory m (pub 4) (LiveStageLink.tagWord w (A.planner i).succ) ∧
    rep.result = some (header A pub m) ∧ rep.probes = 4 ∧ choiceBits rep.events = [] := by
  let n := 2*i.val+3+5
  let v := LiveStageLink.tagWord w (A.planner i).succ
  have ho := ticks_write n (pub 4) v
  dsimp only
  by_cases h : (m (pub 2).val).val < A.initial.length <;>
    simp (config := {decide := true}) only [dispatchReport, h, ↓reduceIte, boot, List.cons_append,
      List.nil_append, List.append_assoc, List.replicate_succ, after, List.foldl_append, List.foldl_cons,
      update, List.foldl_nil, Report.probes, countProbes, choiceBits, true_and]
  all_goals change writeMemory (after m (List.replicate n .tick)) (pub 4) v = _ ∧
    1+(1+(1+countProbes (List.replicate n .tick ++ [.write (pub 4) v]))) = _ ∧
    choiceBits (List.replicate n .tick ++ [.write (pub 4) v]) = []
  all_goals rw [(ticks m n).1,ho.1,ho.2]; exact ⟨rfl,rfl,rfl⟩

theorem closed_effect (pub : Fin 5 → Word w) (m : Memory w) :
    let rep := closedReport pub m
    after m rep.events = m ∧ rep.result = none ∧ rep.probes = 2 ∧ choiceBits rep.events = [] :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- The planner can emit row `o` and the row launcher can read that same
row. The launcher subsequently advances the ordinal. -/
theorem dispatch_ordinal (A : Calendar d) (pub : Fin 5 → Word w) (m : Memory w) (i : Fin A.size)
    (ordTag : pub 2 ≠ pub 4) (totalTag : pub 3 ≠ pub 4) :
    let out := after m (dispatchReport A pub m i).events
    out (pub 2).val = m (pub 2).val ∧ out (pub 3).val = m (pub 3).val ∧
      out (pub 4).val = LiveStageLink.tagWord w (A.planner i).succ := by
  dsimp only
  rw [(dispatch_effect A pub m i).1]
  simp [writeMemory, Fin.val_ne_of_ne ordTag, Fin.val_ne_of_ne totalTag]

/-- The level pointer is an exact natural RAM address when the header fits.
The word before the directory stores the number of words in one level. -/
theorem header_address (A : Calendar d) (pub : Fin 5 → Word w) (m : Memory w)
    (room : (pub 1).val + A.rowPitch*(m (pub 3).val).val + (m (pub 1-1).val).val*A.levelsPerBlock*A.level (m (pub 2).val).val < 2^w) :
    (header A pub m).val =
      (pub 1).val + A.rowPitch*(m (pub 3).val).val + (m (pub 1-1).val).val*A.levelsPerBlock*A.level (m (pub 2).val).val := by
  have hv : ((pub 1).val : Word w) = pub 1 := Fin.ext (Nat.mod_eq_of_lt (pub 1).isLt)
  have ht : ((m (pub 3).val).val : Word w) = m (pub 3).val := Fin.ext (Nat.mod_eq_of_lt (m (pub 3).val).isLt)
  have hg : ((m (pub 1-1).val).val : Word w) = m (pub 1-1).val := Fin.ext (Nat.mod_eq_of_lt (m (pub 1-1).val).isLt)
  unfold header
  conv_lhs => rw [← hg,← hv,← ht,← Nat.cast_mul,← Nat.cast_add,← Nat.cast_mul,← Nat.cast_mul,← Nat.cast_add,Fin.val_natCast,hv,Nat.mod_eq_of_lt room]

/-- For each block below the repetition bound, each slot dispatches to
its own compiled recipe and receives that block's header. -/
theorem execute_block (A : Calendar d) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (blocks t : ℕ) (ht : t < blocks) (i : Fin A.block.length)
    (total : (m (pub 3).val).val = A.total blocks)
    (ord : (m (pub 2).val).val = A.initial.length+t*A.block.length+i.val)
    (room : A.size < 2^w) {cap : ℕ} (hc : 30+2*A.size ≤ cap) :
    let rep := dispatchReport A pub m (i.natAdd A.initial.length)
    execute (machine A pub).program cap ((machine A pub).program.start s) m [] = some rep ∧
      rep.result = some (pub 1+(A.rowPitch : Word w)*m (pub 3).val+(m (pub 1-1).val*(A.levelsPerBlock : Word w))*(t : Word w)) ∧
      after m rep.events = writeMemory m (pub 4) (LiveStageLink.tagWord w A.block[i.val].succ) := by
  have hlt : m (pub 2).val < m (pub 3).val := by
    rw [Fin.lt_def, ord, total, Calendar.total]
    have hi := i.isLt
    have h := Nat.mul_le_mul_right A.block.length (Nat.succ_le_of_lt ht)
    rw [Nat.succ_mul] at h
    omega
  obtain ⟨hp,hl⟩ := A.block_phase t i
  have he := execute_dispatch A pub s m [] hlt (i.natAdd A.initial.length) (ord ▸ hp) room hc
  have hm := (dispatch_effect A pub m (i.natAdd A.initial.length)).1
  refine ⟨he,?_,?_⟩
  · change some (header A pub m) = _
    rw [header, ord, hl]
  · rwa [Calendar.planner_block] at hm

/-- When the last row launcher has advanced the ordinal to the prescribed
total, the next calendar call terminates after two reads. -/
theorem execute_at_total (A : Calendar d) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (blocks : ℕ) (total : (m (pub 3).val).val = A.total blocks)
    (ord : (m (pub 2).val).val = A.total blocks) {cap : ℕ} (hc : 6 ≤ cap) :
    execute (machine A pub).program cap ((machine A pub).program.start s) m [] =
      some (closedReport pub m) :=
  execute_closed A pub s m [] (Fin.le_def.mpr (total.trans ord.symm).le) hc

end CompressorRecords.Schedule.LevelCalendar

end VPVNP
end Computability
end OAI
