import OAI.Computability.VPVNP.CompressorRecordGreedySlots

/-!
# Emitting greedy operand rows from the level's slot tables

Outgoing and incoming mate arrays are indexed by `vertex * degree + port`.
Each cell contains the packed vertex and port at the opposite incidence.
Displacements use the outgoing slot index. Labels use the vertex index.
The row initializer reads exactly one mate, obtains the neighbor by division,
and writes the one or four operand addresses used by the greedy visitor.

Registers 0–7 carry the vertex index, destination cursor, degree, outgoing
and incoming table bases, displacement base, assignment base and zero cell.
The finite public table holds the local slot numbers and is common to all
vertices and all compression levels of the same degree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.SlotGraph

variable {V : Type*} {N w d : ℕ}

/-- The degree and external table addresses used to initialize greedy operand rows from a
level's directed slots. -/
structure PortTables (w : ℕ) where
  /-- The vertex degree, used to pack and unpack a vertex and local port as one word. -/
  degree : Word w
  /-- Base address of the array mapping outgoing ports to their incoming mates. -/
  outgoing : Word w
  /-- Base address of the inverse array mapping incoming ports to their outgoing mates. -/
  incoming : Word w
  /-- Base address of the displacement array indexed by outgoing ports. -/
  displacements : Word w
  /-- Base address of the greedy assignment cells, one per vertex. -/
  labels : Word w
  /-- Address of the cell supplying zero to a padded tag comparison. -/
  zero : Word w

/-- Encode a vertex's ordinal in the supplied vertex order as a machine word. -/
def vertexNumber (order : V ≃ Fin N) (x : V) : Word w := Fin.ofNat _ (order x).val

/-- Encode a vertex and port as the vertex ordinal times the degree plus the local port number. -/
def portNumber (order : V ≃ Fin N) (e : V × Fin d) : Word w :=
  Fin.ofNat _ ((order e.1).val * d + e.2.val)

/-- The level's two directed incidence arrays, including inverse slot numbers. -/
structure PortTables.Represents (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (m : Memory w) : Prop where
  degree : T.degree.val = d
  fits : N * d ≤ 2 ^ w
  vertices : N ≤ 2 ^ w
  outgoing : ∀ e, m (T.outgoing + portNumber order e).val = portNumber order (G.target e)
  incoming : ∀ e, m (T.incoming + portNumber order e).val = portNumber order (G.target.symm e)

/-- The same address convention in the operand-record reader. -/
def PortTables.addresses (T : PortTables w) (order : V ≃ Fin N) : TagAddresses V d w where
  zero := T.zero
  label x := T.labels + vertexNumber order x
  displacement e := T.displacements + portNumber order e

private theorem port_fit (order : V ≃ Fin N) (e : V × Fin d) (fit : N * d ≤ 2 ^ w) :
    (order e.1).val * d + e.2.val < 2 ^ w := by
  have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt (order e.1).isLt)
  rw [Nat.succ_mul] at h
  have := e.2.isLt
  omega

/-- The public constant at index `i` is the word encoding its ordinal, from zero through the
degree. -/
def slotNumbers (w d : ℕ) (i : Fin (d+1)) : Word w := Fin.ofNat _ i.val

private theorem packed_eq {T : PortTables w} {G : SlotGraph V d} {order : V ≃ Fin N}
    {m : Memory w} (rep : T.Represents G order m) (x : V) (i : Fin d) :
    vertexNumber order x * T.degree + slotNumbers w d i.castSucc = portNumber order (x, i) := by
  apply Fin.ext
  have hi : i.val < 2 ^ w := i.isLt.trans (rep.degree ▸ T.degree.isLt)
  have hx := (order x).isLt.trans_le rep.vertices
  have hp := port_fit order (x, i) rep.fits
  have hmul : (order x).val * d < 2 ^ w := (Nat.le_add_right ..).trans_lt hp
  simp [vertexNumber, slotNumbers, portNumber, Fin.val_add, Fin.val_mul, rep.degree,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hmul, Nat.mod_eq_of_lt hp]

private theorem unpack_eq {T : PortTables w} {G : SlotGraph V d} {order : V ≃ Fin N}
    {m : Memory w} (rep : T.Represents G order m) (e : V × Fin d) :
    BinaryOp.div.eval (portNumber order e) T.degree = vertexNumber order e.1 := by
  have hpos : 0 < d := Nat.zero_lt_of_lt e.2.isLt
  have hv : (portNumber (w := w) order e).val = (order e.1).val * d + e.2.val :=
    Nat.mod_eq_of_lt (port_fit order e rep.fits)
  change Fin.ofNat _ ((portNumber (w := w) order e).val / T.degree.val) = _
  rw [hv, rep.degree, Nat.mul_comm (order e.1).val d, Nat.mul_add_div hpos, Nat.div_eq_of_lt e.2.isLt, Nat.add_zero]
  rfl

/-- Operand address formulas sharing the single mate lookup in one row. -/
inductive Operand (d : ℕ) where
  | zero
  | arc
  | increment (remote : Bool) (port : Fin d)
  | neighborLabel

private def localIncrement (remote : Bool) : Option (Fin d) → Operand d
  | none => .zero
  | some i => .increment remote i

/-- List the four operands for a tag exclusion, padding a local test with two zero operands or
including the neighbor's label for a two-end test. -/
def tagOperands : TagTests d → List (Operand d)
  | (_, .inl a) => [.arc, localIncrement false a, .zero, .zero]
  | ((out, _), .inr (a, b)) =>
    [.arc, localIncrement (!out) a, localIncrement out b, .neighborLabel]

/-- Compile the shared endpoint and directed displacement index. -/
def loadMate (out : Bool) (i : Fin d) : List (Op 13 (d+1)) :=
  [.constant 11 1, .publicWord 10 i.castSucc, .binary .mul 8 0 2, .binary .add 8 8 10,
   .binary .add 9 (if out then 3 else 4) 8, .read 9 9, .copy 8 (if out then 8 else 9),
   .binary .div 9 9 2]

private def valueCode : Operand d → List (Op 13 (d+1))
  | .zero => [.copy 10 7]
  | .arc => [.binary .add 10 5 8]
  | .neighborLabel => [.binary .add 10 6 9]
  | .increment remote i =>
    [.binary .mul 10 (if remote then 9 else 0) 2, .publicWord 12 i.castSucc,
     .binary .add 10 10 12, .binary .add 10 5 10]

/-- Emit the computed operand address at the row cursor and advance the cursor by one word. -/
def emitOperand (a : Operand d) : List (Op 13 (d+1)) :=
  valueCode a ++ [.write 1 10, .binary .add 1 1 11]

/-- Initialize one operand row by reading the selected port's mate and emitting the requested
operand addresses in order. -/
def initRow (t : Bool × Fin d) (args : List (Operand d)) : List (Op 13 (d+1)) :=
  loadMate t.1 t.2 ++ args.flatMap emitOperand

/-- Register contract for starting a row, specifying its vertex, destination cursor, degree,
and five table addresses. -/
structure RowInput (T : PortTables w) (vertex dest : Word w) (rs : Regs w 13) : Prop where
  vertex : rs 0 = vertex
  dest : rs 1 = dest
  degree : rs 2 = T.degree
  outgoing : rs 3 = T.outgoing
  incoming : rs 4 = T.incoming
  shifts : rs 5 = T.displacements
  labels : rs 6 = T.labels
  zero : rs 7 = T.zero

/-- Recover the outgoing arc of an incidence, using the inverse slot matching when the
incidence is incoming. -/
def arcOf (G : SlotGraph V d) (x : V) : Bool × Fin d → V × Fin d
  | (true, i) => (x, i)
  | (false, i) => G.target.symm (x, i)

private theorem mate_trace (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (m : Memory w) (rep : T.Represents G order m) (s dest : Word w) (rs : Regs w 13)
    (x : V) (t : Bool × Fin d) (h : RowInput T (vertexNumber order x) dest rs) :
    ∃ es out, trace (slotNumbers w d) s (loadMate t.1 t.2) rs m = some (es, out, m) ∧
      es.length = 8 ∧ countProbes es = 1 ∧
      RowInput T (vertexNumber order x) dest out ∧ out 11 = 1 ∧
      out 8 = portNumber order (arcOf G x t) ∧ out 9 = vertexNumber order (neighbor G x t) := by
  obtain ⟨out, i⟩ := t
  have hpack := packed_eq rep x i
  cases out
  all_goals
    simp (config := {decide := true}) [loadMate, trace, Op.effect, BinaryOp.eval, Function.update,
      countProbes, h.vertex, h.degree, h.outgoing, h.incoming, hpack, rep.outgoing, rep.incoming,
      arcOf, neighbor]
  all_goals
    refine ⟨⟨h.vertex, h.dest, h.degree, h.outgoing, h.incoming, h.shifts, h.labels, h.zero⟩, rfl, ?_⟩
    exact unpack_eq rep _

/-- Resolve a symbolic greedy operand to its address in the zero, displacement, or label table. -/
def operandAddress (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (x : V) (t : Bool × Fin d) : Operand d → Word w
  | .zero => T.zero
  | .arc => T.displacements + portNumber order (arcOf G x t)
  | .increment remote i =>
    T.displacements + portNumber order ((if remote then neighbor G x t else x), i)
  | .neighborLabel => T.labels + vertexNumber order (neighbor G x t)

theorem tagOperands_addresses (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (x : V) (t : TagTests d) :
    (tagOperands t).map (operandAddress T G order x t.1) = tagPointers G (T.addresses order) x t := by
  obtain ⟨⟨out, i⟩, a | ⟨a, b⟩⟩ := t
  · cases out <;> cases a <;> rfl
  · cases out <;> cases a <;> cases b <;> rfl


/-- External writes of the packed output words, starting at the supplied cursor. -/
def writeRow (m : Memory w) (dest : Word w) : List (Word w) → Memory w
  | [] => m
  | v :: vs => writeRow (writeMemory m dest v) (dest + 1) vs

private theorem count_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

private def regValue (rs : Regs w 13) : Operand d → Word w
  | .zero => rs 7
  | .arc => rs 5 + rs 8
  | .neighborLabel => rs 6 + rs 9
  | .increment remote i =>
    rs 5 + (rs (if remote then 9 else 0) * rs 2 + slotNumbers w d i.castSucc)

private theorem emit_trace (s : Word w) (m : Memory w) (rs : Regs w 13)
    (one : rs 11 = 1) (a : Operand d) :
    ∃ es out, trace (slotNumbers w d) s (emitOperand a) rs m =
      some (es, out, writeMemory m (rs 1) (regValue rs a)) ∧
      es.length = (emitOperand a).length ∧ countProbes es = 1 ∧ out 1 = rs 1 + 1 ∧
      ∀ i : Fin 13, i ≠ 1 → i ≠ 10 → i ≠ 12 → out i = rs i := by
  cases a
  case' increment remote i => cases remote
  all_goals
    simp (config := {decide := true}) [trace, Op.effect, emitOperand, valueCode, BinaryOp.eval, one,
      regValue, countProbes, Function.update]
    intro i h1 h10 h12
    simp_all

private theorem emit_list (s : Word w) (m : Memory w) (rs : Regs w 13)
    (one : rs 11 = 1) (args : List (Operand d)) :
    ∃ es out, trace (slotNumbers w d) s (args.flatMap emitOperand) rs m =
        some (es, out, writeRow m (rs 1) (args.map (regValue rs))) ∧
      es.length = (args.flatMap emitOperand).length ∧ countProbes es = args.length ∧
      out 1 = advance (rs 1) args.length ∧
      ∀ i : Fin 13, i ≠ 1 → i ≠ 10 → i ≠ 12 → out i = rs i := by
  induction args generalizing m rs with
  | nil => exact ⟨[], rs, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | cons a args ih =>
    obtain ⟨es, mid, he, hl, hp, hd, keep⟩ := emit_trace s m rs one a
    have hval : regValue (d := d) mid = regValue rs := by
      funext b
      cases b
      case' increment remote i => cases remote
      all_goals simp (config := {decide := true}) [regValue, keep]
    obtain ⟨fs, out, hf, hfl, hfp, hout, finalKeep⟩ := ih (writeMemory m (rs 1) (regValue rs a)) mid
      ((keep 11 (by decide) (by decide) (by decide)).trans one)
    refine ⟨es ++ fs, out, ?_, by simp [hl, hfl], by simp [count_append, hp, hfp, Nat.add_comm], ?_,
      fun i h1 h10 h12 => (finalKeep i h1 h10 h12).trans (keep i h1 h10 h12)⟩
    · simp only [List.flatMap_cons, trace_append, he, Option.bind_some, hf, Option.map_some,
        List.map_cons, writeRow, hd, hval]
    · simpa [advance, hd] using hout

/-- The machine reads one directed mate and writes exactly the specified operand
row. No later lookup in this row depends on the overwritten external cells. -/
theorem initRow_trace (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (m : Memory w) (rep : T.Represents G order m) (s dest : Word w) (rs : Regs w 13)
    (x : V) (t : Bool × Fin d) (h : RowInput T (vertexNumber order x) dest rs) (args : List (Operand d)) :
    ∃ es out, trace (slotNumbers w d) s (initRow t args) rs m =
        some (es, out, writeRow m dest (args.map (operandAddress T G order x t))) ∧
      es.length = (initRow t args).length ∧ countProbes es = 1 + args.length ∧
      RowInput T (vertexNumber order x) (advance dest args.length) out := by
  obtain ⟨es, mid, hm, hl, hp, mi, hu, h8, h9⟩ := mate_trace T G order m rep s dest rs x t h
  have hval : regValue mid = operandAddress T G order x t := by
    funext a
    cases a
    case' increment remote i => cases remote
    all_goals simp only [regValue, operandAddress, mi.zero, mi.shifts, mi.labels, mi.degree, mi.vertex,
      Bool.false_eq_true, ↓reduceIte, h8, h9, packed_eq rep]
  obtain ⟨fs, out, hf, hfl, hfp, hout, hk⟩ := emit_list s m mid hu args
  refine ⟨es ++ fs, out, ?_, ?_, by simp [count_append, hp, hfp], ?_⟩
  · simp [initRow, trace_append, hm, hf, mi.dest, hval]
  · simp [initRow, loadMate, hl, hfl]; omega
  · constructor
    all_goals first
      | simpa [mi.dest] using hout
      | rw [hk _ (by decide) (by decide) (by decide)]; first
          | exact mi.vertex | exact mi.degree | exact mi.outgoing | exact mi.incoming
          | exact mi.shifts | exact mi.labels | exact mi.zero

theorem initRow_length_le (t : Bool × Fin d) (args : List (Operand d)) :
    (initRow t args).length ≤ 8 + 6 * args.length := by
  suffices (args.flatMap emitOperand).length ≤ 6 * args.length by
    rw [initRow, List.length_append, show (loadMate t.1 t.2).length = 8 by rfl]
    omega
  induction args with
  | nil => simp
  | cons a args ih =>
    have ha : (emitOperand a).length ≤ 6 := by cases a <;> simp [emitOperand, valueCode]
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    omega


private theorem next_val (p : Word w) (h : p.val + 1 < 2 ^ w) : (p + 1).val = p.val + 1 := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2 ^ w by omega), Nat.mod_eq_of_lt h]

/-- Sequential writes preserve the complete external memory outside the row. -/
theorem writeRow_outside (m : Memory w) (dest : Word w) (xs : List (Word w)) (addr : ℕ)
    (fit : dest.val + xs.length ≤ 2 ^ w)
    (outside : addr < dest.val ∨ dest.val + xs.length ≤ addr) :
    writeRow m dest xs addr = m addr := by
  induction xs generalizing m dest with
  | nil => rfl
  | cons v vs ih =>
    have hn : addr ≠ dest.val := by simp only [List.length_cons] at outside; omega
    cases vs with
    | nil => simp [writeRow, writeMemory, hn]
    | cons u us =>
      have hd : (dest + 1).val = dest.val + 1 :=
        next_val dest (by simp only [List.length_cons] at fit; omega)
      rw [writeRow, ih _ (dest + 1) (by simp only [hd, List.length_cons] at *; omega)
        (by simp only [hd, List.length_cons] at *; omega)]
      simp [writeMemory, hn]

theorem writeRow_stores (m : Memory w) (dest : Word w) (xs : List (Word w))
    (fit : dest.val + xs.length ≤ 2 ^ w) : Stores (writeRow m dest xs) dest xs := by
  induction xs generalizing m dest with
  | nil => trivial
  | cons v vs ih =>
    cases vs with
    | nil => simp [writeRow, Stores, writeMemory]
    | cons u us =>
      have hd : (dest + 1).val = dest.val + 1 :=
        next_val dest (by simp only [List.length_cons] at fit; omega)
      have hf : (dest + 1).val + (u :: us).length ≤ 2 ^ w := by
        simp only [hd, List.length_cons] at *; omega
      constructor
      · rw [writeRow, writeRow_outside _ _ _ _ hf (.inl (by omega))]
        simp [writeMemory]
      · exact ih _ _ hf

/-- Execution at the normal entry of the compiled word program with the level's
register arguments. Its event log installs the reader's operand words in external
memory and leaves every word outside their address interval unchanged. -/
theorem initRow_native (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (m : Memory w) (rep : T.Represents G order m) (s dest : Word w) (rs : Regs w 13)
    (x : V) (t : Bool × Fin d) (h : RowInput T (vertexNumber order x) dest rs) (args : List (Operand d))
    (fit : dest.val + args.length ≤ 2 ^ w) (priv : Word w → Word w) :
    let code := initRow t args
    let M := (template code 1).instantiate w (slotNumbers w d)
    let words := args.map (operandAddress T G order x t)
    ∃ es, execute M.program (1 + code.length) ⟨M.entry, s, rs, priv⟩ m [] =
        some ⟨es, some (advance dest args.length)⟩ ∧
      after m es = writeRow m dest words ∧ Stores (after m es) dest words ∧
      es.length ≤ 8 + 6 * args.length ∧ countProbes es = 1 + args.length := by
  dsimp only
  obtain ⟨es, out, ht, hl, hp, h1⟩ := initRow_trace T G order m rep s dest rs x t h args
  have hm := trace_after ht
  refine ⟨es, ?_, hm, ?_, hl.le.trans (initRow_length_le t args), hp⟩
  · rw [execute_template, run_eq_trace, ht]
    simp [h1.dest]
  · rw [hm]
    exact writeRow_stores _ _ _ (by simpa using fit)


/-- One output interval is disjoint from both directed mate arrays. -/
def PortTables.Free (T : PortTables w) (order : V ≃ Fin N) (start size : ℕ) : Prop :=
  ∀ e : V × Fin d, ∀ base ∈ [T.outgoing, T.incoming],
    (base + portNumber order e).val < start ∨ start + size ≤ (base + portNumber order e).val

theorem keep_tables (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (m : Memory w) (dest : Word w) (words : List (Word w)) (fit : dest.val + words.length ≤ 2 ^ w)
    (rep : T.Represents G order m) (free : T.Free (d := d) order dest.val words.length) :
    T.Represents G order (writeRow m dest words) := by
  refine ⟨rep.degree, rep.fits, rep.vertices, fun e => ?_, fun e => ?_⟩
  · rw [writeRow_outside _ _ _ _ fit (free e T.outgoing (by simp))]
    exact rep.outgoing e
  · rw [writeRow_outside _ _ _ _ fit (free e T.incoming (by simp))]
    exact rep.incoming e

theorem advance_val (dest : Word w) (n : ℕ) (fit : dest.val + n < 2 ^ w) :
    (advance dest n).val = dest.val + n := by
  induction n generalizing dest with
  | zero => simp [advance]
  | succ n ih =>
    have hv := next_val dest (by omega)
    rw [advance, ih _ (by omega), hv]; omega

private theorem advance_add (dest : Word w) (a b : ℕ) :
    advance dest (a + b) = advance (advance dest a) b := by
  induction a generalizing dest with
  | zero => simp [advance]
  | succ a ih => rw [Nat.succ_add, advance, advance, ih]

theorem writeRow_append (m : Memory w) (dest : Word w) (xs ys : List (Word w)) :
    writeRow m dest (xs ++ ys) = writeRow (writeRow m dest xs) (advance dest xs.length) ys := by
  induction xs generalizing m dest with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, writeRow, List.length_cons, advance, ih]

/-- The ordered incidence and operand lists used to initialize one vertex's greedy record. -/
abbrev OperandRows (d : ℕ) := List ((Bool × Fin d) × List (Operand d))

/-- Flatten the resolved operand addresses of all rows for a vertex in their emission order. -/
def rowWords (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N) (x : V)
    (rows : OperandRows d) : List (Word w) :=
  rows.flatMap fun row => row.2.map (operandAddress T G order x row.1)

/-- Concatenate the native row initializers in the order of the supplied incidence rows. -/
def initRows (rows : OperandRows d) : List (Op 13 (d+1)) :=
  rows.flatMap fun row => initRow row.1 row.2

theorem initRows_trace (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (s : Word w) (x : V) (rows : OperandRows d) (m : Memory w) (dest : Word w) (rs : Regs w 13)
    (h : RowInput T (vertexNumber order x) dest rs) (rep : T.Represents G order m)
    (fit : dest.val + (rowWords T G order x rows).length < 2 ^ w)
    (free : T.Free (d := d) order dest.val (rowWords T G order x rows).length) :
    let words := rowWords T G order x rows
    ∃ es out, trace (slotNumbers w d) s (initRows rows) rs m =
        some (es, out, writeRow m dest words) ∧
      es.length = (initRows rows).length ∧ countProbes es = rows.length + words.length ∧
      RowInput T (vertexNumber order x) (advance dest words.length) out := by
  induction rows generalizing m dest rs with
  | nil => exact ⟨[], rs, rfl, rfl, rfl, h⟩
  | cons row rows ih =>
    dsimp only
    obtain ⟨t, args⟩ := row
    let words := args.map (operandAddress T G order x t)
    let rest := rowWords T G order x rows
    have hwords : rowWords T G order x ((t, args) :: rows) = words ++ rest := rfl
    have len : words.length = args.length := List.length_map _
    rw [hwords, List.length_append] at fit free
    have hd : (advance dest words.length).val = dest.val + words.length := advance_val dest _ (by omega)
    have left : T.Free (d := d) order dest.val words.length := fun e b hb => by
      obtain hl | hr := free e b hb
      · exact Or.inl hl
      · exact Or.inr (by omega)
    have right : T.Free (d := d) order (advance dest words.length).val rest.length := fun e b hb => by
      obtain hl | hr := free e b hb
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    obtain ⟨es, mid, he, hl, hp, hm⟩ := initRow_trace T G order m rep s dest rs x t h args
    obtain ⟨fs, out, hf, hfl, hfp, ho⟩ := ih (writeRow m dest words) (advance dest words.length) mid
      (by simpa only [len] using hm) (keep_tables T G order m dest words (by omega) rep left)
      (by change (advance dest words.length).val + rest.length < _; omega) right
    refine ⟨es ++ fs, out, ?_, ?_, ?_, ?_⟩
    · simp only [initRows, List.flatMap_cons, hwords, writeRow_append, trace_append, he,
        Option.bind_some]
      change (trace (slotNumbers w d) s (initRows rows) mid (writeRow m dest words)).map _ = _
      rw [hf]; rfl
    · simp only [List.length_append, hl, hfl, initRows, List.flatMap_cons]
    · rw [count_append, hp, hfp, hwords, List.length_append, List.length_cons, len]
      change 1 + args.length + (rows.length + rest.length) = _
      omega
    · simpa only [hwords, List.length_append, advance_add] using ho

theorem initRows_length_le (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (x : V) (rows : OperandRows d) :
    (initRows rows).length ≤ 8 * rows.length + 6 * (rowWords T G order x rows).length := by
  induction rows with
  | nil => simp [initRows, rowWords]
  | cons row rows ih =>
    change ((initRow row.1 row.2) ++ initRows rows).length ≤
      8 * (rows.length + 1) + 6 * ((row.2.map _ ++ rowWords T G order x rows).length)
    rw [List.length_append, List.length_append, List.length_map, Nat.mul_add, Nat.mul_add]
    have h := initRow_length_le row.1 row.2
    omega

/-- A single fixed instruction table emits every forbidden pointer for a vertex,
retaining the current external memory between rows. -/
theorem initRows_native (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (s : Word w) (x : V) (rows : OperandRows d) (m : Memory w) (dest : Word w) (rs : Regs w 13)
    (h : RowInput T (vertexNumber order x) dest rs) (rep : T.Represents G order m)
    (fit : dest.val + (rowWords T G order x rows).length < 2 ^ w)
    (free : T.Free (d := d) order dest.val (rowWords T G order x rows).length)
    (priv : Word w → Word w) :
    let code := initRows rows
    let M := (template code 1).instantiate w (slotNumbers w d)
    let words := rowWords T G order x rows
    ∃ es, execute M.program (1 + code.length) ⟨M.entry, s, rs, priv⟩ m [] =
        some ⟨es, some (advance dest words.length)⟩ ∧
      after m es = writeRow m dest words ∧ Stores (after m es) dest words ∧
      es.length ≤ 8 * rows.length + 6 * words.length ∧ countProbes es = rows.length + words.length := by
  dsimp only
  obtain ⟨es, out, ht, hl, hp, h1⟩ := initRows_trace T G order s x rows m dest rs h rep fit free
  have hm := trace_after ht
  refine ⟨es, ?_, hm, ?_, hl.le.trans (initRows_length_le T G order x rows), hp⟩
  · rw [execute_template, run_eq_trace, ht]
    simp [h1.dest]
  · rw [hm]
    exact writeRow_stores _ _ _ fit.le


/-- The two vertex programs use the exact exclusion order of the greedy reader. -/
def colorOperandRows (d : ℕ) : OperandRows d :=
  (incidences d).map (fun t => (t, [.neighborLabel]))

/-- Enumerate the four-operand rows for all tag exclusions of a degree-`d` vertex. -/
def tagOperandRows (d : ℕ) : OperandRows d :=
  (tagTests d).map (fun t => (t.1, tagOperands t))

theorem rowWords_color (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N) (x : V) :
    rowWords T G order x (colorOperandRows d) = (colorRows G x (T.addresses (d := d) order).label).flatten := by
  simp [rowWords, colorOperandRows, colorRows, operandAddress, PortTables.addresses,
    Function.comp_def, List.flatMap_def]

theorem rowWords_tag (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N) (x : V) :
    rowWords T G order x (tagOperandRows d) =
      ((tagTests d).map (tagPointers G (T.addresses order) x)).flatten := by
  simp [rowWords, tagOperandRows, Function.comp_def, List.flatMap_def, tagOperands_addresses]

theorem rowWords_color_length (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N) (x : V) :
    (rowWords T G order x (colorOperandRows d)).length = 2 * d := by
  simp [rowWords, colorOperandRows, List.flatMap_map]

theorem rowWords_tag_length (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N) (x : V) :
    (rowWords T G order x (tagOperandRows d)).length = (tagTests d).length * 4 := by
  have h (t : TagTests d) : (tagOperands t).length = 4 := by
    obtain ⟨⟨b,i⟩, a | ⟨a,c⟩⟩ := t <;> rfl
  simp [rowWords, tagOperandRows, List.flatMap_map, h]

end CompressorRecords.Greedy

end VPVNP
end Computability
end OAI
