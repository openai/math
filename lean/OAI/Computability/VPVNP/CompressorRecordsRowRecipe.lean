import OAI.Computability.VPVNP.CompressorRecordGreedyInit
import OAI.Computability.VPVNP.LiveOneShot
import Mathlib.Tactic.Ring

/-!
# Computing a compressor worker row from a live level header

A recipe is a finite straight-line word program. It may read a public word,
the current level pointer carried in persistent state, or external memory
through any computed address. Its assignments finish before it writes the
destination row, so its values describe the input memory even when a row
overlaps cells used to compute it. Two additional registers hold the output
cursor and the constant one.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RowRecipe

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {r k g w : ℕ}

/-- Read-only assignments in the straight-line source program. The native
two-bit immediates may be combined by arithmetic to build larger constants. -/
inductive RHS (r k : ℕ) where
  | literal (v : Word 2)
  | publicWord (i : Fin k)
  | state
  | copy (src : Fin r)
  | binary (op : BinaryOp) (lhs rhs : Fin r)
  | read (address : Fin r)

/-- One straight-line planner instruction that evaluates a read-only right-hand side and stores
its word in a specified register. -/
structure Assign (r k : ℕ) where
  /-- Register overwritten by this assignment before the next recipe line executes. -/
  dst : Fin r
  /-- Read-only operation that supplies the word assigned to the destination register. -/
  rhs : RHS r k

/-- Compute an assignment's word from the public operands, persistent state, external memory
and current registers. -/
def RHS.value (pub : Fin k → Word w) (s : Word w) (m : Memory w) (rs : Regs w r) :
    RHS r k → Word w
  | .literal v => Fin.ofNat _ v.val
  | .publicWord i => pub i
  | .state => s
  | .copy src => rs src
  | .binary op a b => op.eval (rs a) (rs b)
  | .read a => m (rs a).val

/-- The assignment's trace event, a memory read carrying its address and observed word for a
load, or one private tick for another operation. -/
def RHS.event (m : Memory w) (rs : Regs w r) : RHS r k → Event w
  | .read a => .read (rs a) (m (rs a).val)
  | _ => .tick

/-- Number of external reads charged for one right-hand side, one for a memory load and zero
for all register operations and inputs. -/
def RHS.reads : RHS r k → ℕ
  | .read _ => 1
  | _ => 0

/-- Execute the assignments in order against the same entry memory, returning the chronological
events and the final register values. -/
def evaluate (pub : Fin k → Word w) (s : Word w) (m : Memory w) :
    List (Assign r k) → Regs w r → List (Event w) × Regs w r
  | [], rs => ([],rs)
  | a :: rest, rs =>
    let next := evaluate pub s m rest (Function.update rs a.dst (a.rhs.value pub s m rs))
    (a.rhs.event m rs :: next.1, next.2)

/-- The selected registers specify both the destination and the full padded row. -/
structure Recipe (r k g : ℕ) where
  /-- Straight-line assignments that compute the destination address and field values before
  any directory word is written. -/
  lines : List (Assign r k)
  /-- Register containing the address at which to write the first word of the directory row. -/
  dest : Fin r
  /-- Register containing the stage tag that selects the worker for this row. -/
  tag : Fin r
  /-- Register containing the cursor passed to the worker on its first call. -/
  start : Fin r
  /-- Register containing the exclusive stopping cursor for the worker's scan. -/
  stop : Fin r
  /-- Registers containing the worker's parameter words in their padded directory order. -/
  params : Fin g → Fin r

/-- Output registers in the order their contents are stored, starting with the tag and both
cursor bounds and ending with the parameter bank. -/
def Recipe.fields (R : Recipe r k g) := R.tag :: R.start :: R.stop :: List.ofFn R.params

/-- The register file obtained by running the recipe's assignments from zeroed registers on the
supplied public words, state and entry memory. -/
def Recipe.values (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) :=
  (evaluate pub s m R.lines (fun _ ↦ 0)).2

/-- The computed destination address read from the final register file before row storage
begins. -/
def Recipe.address (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) :=
  R.values pub s m R.dest

/-- The words written to the directory, read from the final registers in tag, start, stop and
parameter order. -/
def Recipe.words (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) :=
  R.fields.map (R.values pub s m)

private def low (i : Fin r) := i.castAdd 2
private def ptr (r : ℕ) := (0 : Fin 2).natAdd r
private def one (r : ℕ) := (1 : Fin 2).natAdd r

private def Assign.code (a : Assign r k) : Op (r+2) k := match a.rhs with
  | .literal v => .constant (low a.dst) v
  | .publicWord i => .publicWord (low a.dst) i
  | .state => .stateWord (low a.dst)
  | .copy i => .copy (low a.dst) (low i)
  | .binary op i j => .binary op (low a.dst) (low i) (low j)
  | .read i => .read (low a.dst) (low i)

private def storeCode (i : Fin r) : List (Op (r+2) k) :=
  [.write (ptr r) (low i), .binary .add (ptr r) (ptr r) (one r)]

/-- Compile the assignments, write the fields to consecutive cells, and put the incoming state
plus one in the return register. -/
def Recipe.code (R : Recipe r k g) : List (Op (r+2) k) :=
  R.lines.map Assign.code ++ ([.copy (ptr r) (low R.dest), .constant (one r) 1] ++
    (R.fields.flatMap storeCode ++ [.stateWord (ptr r), .binary .add (ptr r) (ptr r) (one r)]))

/-- Native instruction template for publishing one recipe row and returning the advanced state. -/
def Recipe.table (R : Recipe r k g) := template R.code (ptr r)

private def storeLog (dest : Word w) : List (Word w) → List (Event w)
  | [] => []
  | v :: vs => .write dest v :: .tick :: storeLog (dest+1) vs

/-- Trace of the recipe's assignment events, pointer setup, consecutive row writes and state
advance, with return value `s + 1`. -/
def Recipe.report (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) : Report w :=
  ⟨(evaluate pub s m R.lines (fun _ ↦ 0)).1 ++ [.tick,.tick] ++
    storeLog (R.address pub s m) (R.words pub s m) ++ [.tick,.tick],some (s+1)⟩

/-- Total external reads performed by the computation lines before the row is written, counting
repeated loads separately. -/
def Recipe.reads (R : Recipe r k g) : ℕ := (R.lines.map fun a ↦ a.rhs.reads).sum

private theorem update_left {a b : ℕ} {α : Type*} (l : Fin a → α) (h : Fin b → α)
    (i : Fin a) (v : α) :
    Function.update (Fin.append l h) (i.castAdd b) v = Fin.append (Function.update l i v) h := by
  funext t
  cases t using Fin.addCases with
  | left j => by_cases e : j = i <;> simp [Function.update, e]
  | right j =>
    have e : j.natAdd a ≠ i.castAdd b := fun eqn ↦ by have := congrArg Fin.val eqn; simp at this; omega
    simp [Function.update_of_ne e]

private theorem update_right {a b : ℕ} {α : Type*} (l : Fin a → α) (h : Fin b → α)
    (i : Fin b) (v : α) :
    Function.update (Fin.append l h) (i.natAdd a) v = Fin.append l (Function.update h i v) := by
  funext t
  cases t using Fin.addCases with
  | left j =>
    have e : j.castAdd b ≠ i.natAdd a := fun eqn ↦ by have := congrArg Fin.val eqn; simp at this; omega
    simp [Function.update_of_ne e]
  | right j => by_cases e : j = i <;> simp [Function.update, e]

private theorem assign_effect (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (rs : Regs w r) (aux : Fin 2 → Word w) (a : Assign r k) :
    a.code.effect pub s (Fin.append rs aux) m = some (a.rhs.event m rs,
      Fin.append (Function.update rs a.dst (a.rhs.value pub s m rs)) aux, m) := by
  obtain ⟨i,x⟩ := a
  cases x <;> simp [Assign.code, RHS.value, RHS.event, Op.effect, low, update_left]

private theorem lines_trace (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (ls : List (Assign r k)) (rs : Regs w r) (aux : Fin 2 → Word w) :
    let out := evaluate pub s m ls rs
    trace pub s (ls.map Assign.code) (Fin.append rs aux) m = some (out.1,Fin.append out.2 aux,m) := by
  induction ls generalizing rs with
  | nil => rfl
  | cons a ls ih => simp [trace, assign_effect, ih, evaluate]

private theorem store_trace (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (rs : Regs w r) (aux : Fin 2 → Word w) (h : aux 1 = 1) (fields : List (Fin r)) :
    let words := fields.map rs
    ∃ last : Fin 2 → Word w, last 1 = 1 ∧
      trace pub s (fields.flatMap storeCode) (Fin.append rs aux) m =
        some (storeLog (aux 0) words,Fin.append rs last,Greedy.writeRow m (aux 0) words) := by
  induction fields generalizing m aux with
  | nil => exact ⟨aux,h,rfl⟩
  | cons i rest ih =>
    let aux' := Function.update aux 0 (aux 0+1)
    have h' : aux' 1 = 1 := by simpa (config := {decide := true}) [aux']
    obtain ⟨last,hl,ht⟩ := ih (writeMemory m (aux 0) (rs i)) aux' h'
    refine ⟨last,hl,?_⟩
    simp [storeCode, trace, Op.effect, ptr, low, one, update_right, BinaryOp.eval, h, ← show
      Function.update aux 0 (aux 0+1) = aux' by rfl, ht, storeLog, Greedy.writeRow, aux']

private theorem zeros : (fun _ : Fin (r+2) ↦ (0 : Word w)) =
    Fin.append (fun _ : Fin r ↦ 0) (fun _ : Fin 2 ↦ 0) := by
  funext i; cases i using Fin.addCases <;> simp

private theorem row_trace (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) :
    ∃ out, trace pub s R.code (fun _ ↦ 0) m = some ((R.report pub s m).events,out,
      Greedy.writeRow m (R.address pub s m) (R.words pub s m)) ∧ out (ptr r) = s+1 := by
  let rs := R.values pub s m
  let aux : Fin 2 → Word w := Function.update (Function.update (fun _ ↦ 0) 0 (rs R.dest)) 1 1
  have h : aux 1 = 1 := by simp [aux]
  obtain ⟨last,hl,ht⟩ := store_trace pub s m rs aux h R.fields
  unfold Recipe.code
  rw [zeros, trace_append, lines_trace]
  dsimp only [Option.bind_some]
  change ∃ _, ((trace pub s _ (Fin.append rs _) m).map _) = _ ∧ _
  simp only [List.cons_append, List.nil_append, trace, Op.effect, ptr, low, one, Fin.append_left,
    update_right, bind, Option.bind_some]
  have lit : Fin.ofNat (2^w) (1 : Word 2).val = (1 : Word w) := by apply Fin.ext; rfl
  rw [lit, trace_append, ht]
  simp [trace, Op.effect, BinaryOp.eval, Fin.append_right, update_right, hl,
    Recipe.report, Recipe.address, Recipe.words, rs, aux, List.append_assoc]

private theorem eval_cost (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (ls : List (Assign r k)) (rs : Regs w r) :
    (evaluate pub s m ls rs).1.length = ls.length ∧
      countProbes (evaluate pub s m ls rs).1 = (ls.map fun a ↦ a.rhs.reads).sum := by
  induction ls generalizing rs with
  | nil => exact ⟨rfl,rfl⟩
  | cons a ls ih =>
    obtain ⟨hl,hp⟩ := ih (Function.update rs a.dst (a.rhs.value pub s m rs))
    cases a with
    | mk dst rhs =>
      cases rhs <;> simp [evaluate, RHS.event, RHS.reads, hl, hp, countProbes]

private theorem store_cost (dest : Word w) (vs : List (Word w)) :
    (storeLog dest vs).length = 2*vs.length ∧ countProbes (storeLog dest vs) = vs.length := by
  induction vs generalizing dest with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨hl,hp⟩ := ih (dest+1)
    simp [storeLog, countProbes, hl, hp, Nat.add_comm]
    omega

theorem fields_length (R : Recipe r k g) : R.fields.length = g+3 := by simp [Recipe.fields]

private theorem storeCode_length (fs : List (Fin r)) :
    (fs.flatMap (storeCode (k := k))).length = 2*fs.length := by
  induction fs with
  | nil => rfl
  | cons x xs ih => simp [storeCode, ih, Nat.mul_succ]

theorem code_length (R : Recipe r k g) : R.code.length = R.lines.length + 2*(g+3)+4 := by
  simp only [Recipe.code, List.length_append, List.length_map, storeCode_length, fields_length,
    List.length_cons, List.length_nil]
  omega

/-- Exact native execution, including the rejection of every nonempty branch stream. -/
theorem execute_row (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (cap : ℕ) (budget : R.code.length < cap) :
    let M := R.table.instantiate w pub
    execute M.program cap (M.program.start s) m bits =
      if bits = [] then some (R.report pub s m) else none := by
  obtain ⟨f,rfl⟩ : ∃ f, cap = (f+1) + R.code.length := ⟨cap-(1+R.code.length),by omega⟩
  let M := (template R.code (ptr r)).instantiate w pub
  let bad : Fin (R.code.length+2) := ⟨R.code.length+1,by omega⟩
  let stop : Fin (R.code.length+2) := ⟨R.code.length,by omega⟩
  have hb : M.code bad = .reject := by
    simp [M, bad, template, Template.instantiate, Instr.resize, show ¬R.code.length+1 < R.code.length by omega]
  have hs : M.code stop = .returnState (ptr r) := by simp [M, stop, template, Template.instantiate, Instr.resize]
  have step := (template_contains R.code (ptr r) pub).execute hb s (fun _ ↦ 0) (fun _ ↦ 0) m bits (f+1)
  obtain ⟨out,ht,hv⟩ := row_trace R pub s m
  change execute M.program _ ⟨⟨0,by omega⟩,s,fun _ ↦ 0,fun _ ↦ 0⟩ m bits = _
  rw [step, run_eq_trace]
  change (trace pub s R.code (fun _ ↦ 0) m).bind _ = _
  rw [ht]
  change (execute M.program (f+1) ⟨stop,s,out,fun _ ↦ 0⟩ _ bits).map _ = _
  by_cases h : bits = [] <;> simp [execute, Machine.program, hs, Instr.run, h, hv, Recipe.report]

/-- One-shot version of the row publisher that accepts after the row is stored so the linked
launcher can take control. -/
def Recipe.acceptTable (R : Recipe r k g) := LiveOneShot.oneShot R.table

/-- Single-row planners transfer to a statically linked launch stage on acceptance. -/
theorem execute_accept (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (cap : ℕ) (budget : R.code.length < cap) :
    let M := R.acceptTable.instantiate w pub
    execute M.program cap (M.program.start s) m bits =
      if bits = [] then some ⟨(R.report pub s m).events,none⟩ else none := by
  dsimp only [Recipe.acceptTable]
  rw [LiveOneShot.execute_oneShot]
  change (execute (R.table.instantiate w pub).program cap ((R.table.instantiate w pub).program.start s)
    m bits).map _ = _
  rw [execute_row R pub s m bits cap budget]
  split <;> rfl

theorem report_cost (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) :
    (R.report pub s m).events.length = R.lines.length + 2*(g+3)+4 ∧
      (R.report pub s m).probes = R.reads+(g+3) ∧ choiceBits (R.report pub s m).events = [] := by
  have he := execute_row R pub s m [] (R.code.length+1) (by omega)
  have hchoice := (execute_spec (show execute _ _ _ _ [] = some (R.report pub s m) from he)).2.2
  obtain ⟨hl,hp⟩ := eval_cost pub s m R.lines (fun _ ↦ 0)
  obtain ⟨wl,wp⟩ := store_cost (R.address pub s m) (R.words pub s m)
  have wh : (R.words pub s m).length = g+3 := by simp [Recipe.words, fields_length]
  refine ⟨?_,?_,hchoice⟩
  · simp only [Recipe.report, List.length_append, wl, wh, hl, List.length_cons, List.length_nil]
    omega
  · simp [Recipe.report, Report.probes, Greedy.probes_append, countProbes, wp, wh, hp, Recipe.reads]

theorem after_row (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) :
    after m (R.report pub s m).events = Greedy.writeRow m (R.address pub s m) (R.words pub s m) := by
  obtain ⟨out,ht,_⟩ := row_trace R pub s m
  exact Greedy.trace_after ht

/-- Every field is computed from entry memory. No disjointness between metadata
and the destination row is needed to install the result. -/
theorem row_stores (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (fit : (R.address pub s m).val + (g+3) ≤ 2^w) :
    Greedy.Stores (after m (R.report pub s m).events) (R.address pub s m) (R.words pub s m) := by
  rw [after_row]
  exact Greedy.writeRow_stores _ _ _ (by simpa [Recipe.words, fields_length] using fit)

theorem row_outside (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (fit : (R.address pub s m).val + (g+3) ≤ 2^w) (a : ℕ)
    (free : a < (R.address pub s m).val ∨ (R.address pub s m).val + (g+3) ≤ a) :
    after m (R.report pub s m).events a = m a := by
  rw [after_row]
  exact Greedy.writeRow_outside _ _ _ _
    (by simpa [Recipe.words, fields_length] using fit) (by simpa [Recipe.words, fields_length] using free)

/-- The four consecutive live level-header words are the vertex count, degree,
replication factor, and directory row ordinal. Public word zero is the directory
base. The emitted row for tag one starts at zero and stops at the slot count. -/
def sizeRecipe : Recipe 11 1 2 where
  lines :=
    [⟨0,.state⟩, ⟨1,.literal 1⟩, ⟨2,.read 0⟩, ⟨0,.binary .add 0 1⟩, ⟨3,.read 0⟩,
     ⟨0,.binary .add 0 1⟩, ⟨4,.read 0⟩, ⟨0,.binary .add 0 1⟩, ⟨5,.read 0⟩,
     ⟨6,.binary .mul 2 3⟩, ⟨6,.binary .mul 6 4⟩, ⟨7,.binary .mul 6 3⟩, ⟨8,.publicWord 0⟩,
     ⟨9,.literal 2⟩, ⟨10,.literal 3⟩, ⟨9,.binary .add 9 10⟩, ⟨9,.binary .mul 5 9⟩,
     ⟨8,.binary .add 8 9⟩, ⟨10,.literal 0⟩]
  dest := 8
  tag := 1
  start := 10
  stop := 7
  params := ![6,3]

theorem sizeRecipe_values (pub : Fin 1 → Word w) (s : Word w) (m : Memory w) :
    let V := m s.val
    let D := m (s+1).val
    let R := m (s+2).val
    let B := V*D*R
    let S := B*D
    sizeRecipe.address pub s m = pub 0 + m (s+3).val * 5 ∧
      sizeRecipe.words pub s m = [1,0,S,B,D] := by
  have two : (s+1+1 : Word w) = s+2 := by rw [add_assoc, one_add_one_eq_two]
  have three : (s+2+1 : Word w) = s+3 := by ring
  have five : (2+3 : Word w) = 5 := by ring
  simp (config := {decide := true}) [Recipe.address, Recipe.words, Recipe.fields, Recipe.values,
    sizeRecipe, evaluate, RHS.value, BinaryOp.eval, two, three, five]

/-- Native construction of the slot-scan row using four metadata reads and five
writes. The row's stop and operands are evaluated from the original header. -/
theorem sizeRecipe_row (pub : Fin 1 → Word w) (s : Word w) (m : Memory w)
    (fit : (pub 0 + m (s+3).val * 5).val + 5 ≤ 2^w) :
    let M := sizeRecipe.acceptTable.instantiate w pub
    let B := m s.val * m (s+1).val * m (s+2).val
    let es := (sizeRecipe.report pub s m).events
    execute M.program 34 (M.program.start s) m [] = some ⟨es,none⟩ ∧
      Greedy.Stores (after m es) (pub 0 + m (s+3).val*5) [1,0,B*m (s+1).val,B,m (s+1).val] ∧
      countProbes es = 9 := by
  obtain ⟨ha,hw⟩ := sizeRecipe_values pub s m
  refine ⟨execute_accept sizeRecipe pub s m [] 34 (by decide), ?_, ?_⟩
  · rw [← ha, ← hw]
    exact row_stores _ _ _ _ (by simpa only [ha] using fit)
  · exact (report_cost sizeRecipe pub s m).2.1

end CompressorRecords.RowRecipe

end VPVNP
end Computability
end OAI
