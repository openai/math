import OAI.Computability.VPVNP.RAMUniform

/-!
# Straight-line word code for the preorder counter

Each operation emits one instruction of the finite burst machine. Guards jump to
the program's reject instruction. The same block may occupy any prescribed
sequence of program counters, so stack and counter operations can be inserted
between the loops which read nondeterministic grammar choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM BurstRAM.PrivateRAM

variable {p r k w : ℕ}

/-- Operands of a straight-line instruction, with a two-bit literal format. -/
inductive Op (r k : ℕ) where
  | constant (dst : Fin r) (value : Word 2)
  | publicWord (dst : Fin r) (i : Fin k)
  | stateWord (dst : Fin r)
  | copy (dst src : Fin r)
  | binary (op : BinaryOp) (dst lhs rhs : Fin r)
  | read (dst addr : Fin r)
  | write (addr src : Fin r)
  | guardEq (lhs rhs : Fin r)
  | guardLt (lhs rhs : Fin r)

/-- Translate one line using the successor and rejecting program counters. -/
def Op.emit (next bad : Fin p) : Op r k → Instr 2 p r k
  | .constant dst v => .constant dst v next
  | .publicWord dst i => .publicWord dst i next
  | .stateWord dst => .stateWord dst next
  | .copy dst src => .copy dst src next
  | .binary op dst x y => .binary op dst x y next
  | .read dst a => .readExternal dst a next
  | .write a s => .writeExternal a s next
  | .guardEq x y => .jumpEq x y next bad
  | .guardLt x y => .jumpLt x y next bad

/-- Contents of the `r` private registers, each holding a width-`w` word. -/
abbrev Regs (w r : ℕ) := Fin r → Word w
/-- Continuation that takes the current register file and external memory and returns an
optional burst report. -/
abbrev Cont (w r : ℕ) := Regs w r → Memory w → Option (Report w)

/-- Register, external-memory and event semantics of one line. -/
def Op.effect (pub : Fin k → Word w) (state : Word w) (op : Op r k)
    (regs : Regs w r) (mem : Memory w) : Option (Event w × Regs w r × Memory w) :=
  match op with
  | .constant dst v => some (.tick, Function.update regs dst (Fin.ofNat _ v.val), mem)
  | .publicWord dst i => some (.tick, Function.update regs dst (pub i), mem)
  | .stateWord dst => some (.tick, Function.update regs dst state, mem)
  | .copy dst src => some (.tick, Function.update regs dst (regs src), mem)
  | .binary op dst x y => some (.tick, Function.update regs dst (op.eval (regs x) (regs y)), mem)
  | .read dst a =>
    let v := mem (regs a).val
    some (.read (regs a) v, Function.update regs dst v, mem)
  | .write a s => some (.write (regs a) (regs s), regs, writeMemory mem (regs a) (regs s))
  | .guardEq x y => if regs x = regs y then some (.tick, regs, mem) else none
  | .guardLt x y => if regs x < regs y then some (.tick, regs, mem) else none

/-- Execute one straight-line operation, pass the resulting registers and memory to the
continuation, and prepend its event to a successful report. -/
def Op.run (pub : Fin k → Word w) (state : Word w) (op : Op r k) (next : Cont w r) :
    Cont w r := fun regs mem ↦ (op.effect pub state regs mem).bind fun (e, rs, m) =>
      (next rs m).map (Report.prepend e)

/-- Execute the straight-line block in list order before invoking the continuation with its
final registers and memory. -/
def run (ops : List (Op r k)) (pub : Fin k → Word w) (state : Word w) (next : Cont w r) :
    Cont w r := ops.foldr (Op.run pub state) next

theorem run_append (a b : List (Op r k)) (pub : Fin k → Word w) (state : Word w) (next : Cont w r) :
    run (a ++ b) pub state next = run a pub state (run b pub state next) := by simp [run]

/-- Evaluate a whole block, retaining the post-state for a subsequent block. -/
def trace (pub : Fin k → Word w) (state : Word w) :
    List (Op r k) → Regs w r → Memory w → Option (List (Event w) × Regs w r × Memory w)
  | [], rs, m => some ([], rs, m)
  | op :: rest, rs, m => do
    let (e, rs, m) ← op.effect pub state rs m
    let (es, rs, m) ← trace pub state rest rs m
    return (e :: es, rs, m)

theorem run_eq_trace (ops : List (Op r k)) (pub : Fin k → Word w) (state : Word w)
    (next : Cont w r) (regs : Regs w r) (mem : Memory w) :
    run ops pub state next regs mem =
      (trace pub state ops regs mem).bind fun (es, rs, m) =>
        (next rs m).map fun t => ⟨es ++ t.events, t.result⟩ := by
  induction ops generalizing regs mem with
  | nil => simp [run, trace]
  | cons op ops ih =>
    change op.run pub state (run ops pub state next) regs mem = _
    cases he : op.effect pub state regs mem with
    | none => simp [Op.run, trace, he]
    | some a =>
      obtain ⟨e, rs, m⟩ := a
      cases ht : trace pub state ops rs m with
      | none => simp [Op.run, trace, he, ih rs m, ht]
      | some a =>
        obtain ⟨es, rs', m'⟩ := a
        cases hn : next rs' m' <;> simp [Op.run, trace, he, ih rs m, ht, hn, Report.prepend]

/-- Concatenation runs the two blocks with the actual intermediate registers and memory. -/
theorem trace_append (pub : Fin k → Word w) (state : Word w) (a b : List (Op r k))
    (regs : Regs w r) (mem : Memory w) :
    trace pub state (a ++ b) regs mem =
      (trace pub state a regs mem).bind fun (es, rs, m) =>
        (trace pub state b rs m).map fun (fs, rs', m') => (es ++ fs, rs', m') := by
  induction a generalizing regs mem with
  | nil => simp [trace]
  | cons op a ih =>
    cases he : op.effect pub state regs mem with
    | none => simp [trace, he]
    | some t =>
      obtain ⟨e, rs, m⟩ := t
      cases ht : trace pub state a rs m with
      | none => simp [trace, he, ih, ht]
      | some t =>
        obtain ⟨es, rs', m'⟩ := t
        cases hf : trace pub state b rs' m' <;> simp [trace, he, ih, ht, hf]

/-- Registers available to surrounding blocks when no line names them as its destination. -/
def Op.destination : Op r k → Option (Fin r)
  | .constant i _ | .publicWord i _ | .stateWord i | .copy i _
  | .binary _ i _ _ | .read i _ => some i
  | .write .. | .guardEq .. | .guardLt .. => none

theorem trace_preserves {pub : Fin k → Word w} {state : Word w} {ops : List (Op r k)}
    {regs rs : Regs w r} {mem m : Memory w} {es : List (Event w)} {i : Fin r}
    (hw : ∀ op ∈ ops, op.destination ≠ some i)
    (ht : trace pub state ops regs mem = some (es, rs, m)) : rs i = regs i := by
  induction ops generalizing regs mem es with
  | nil => simp [trace] at ht; rw [ht.2.1]
  | cons op ops ih =>
    cases he : op.effect pub state regs mem with
    | none => simp [trace, he] at ht
    | some t =>
      obtain ⟨e, r₁, m₁⟩ := t
      cases hs : trace pub state ops r₁ m₁ with
      | none => simp [trace, he, hs] at ht
      | some t =>
        obtain ⟨es', r₂, m₂⟩ := t
        simp [trace, he, hs] at ht
        obtain ⟨_, rfl, rfl⟩ := ht
        rw [ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) hs]
        have hd := hw op (List.mem_cons_self ..)
        cases op <;> simp [Op.effect, Op.destination] at he hd
        all_goals first
          | exact congrFun he.2.1.symm i
          | rw [← he.2.1]; exact Function.update_of_ne (Ne.symm hd) _ _
          | exact congrFun he.2.2.1.symm i

/-- Occurrence of a block inside a possibly larger, looping instruction table. -/
inductive Contains (M : Machine w p r k) (bad : Fin p) : Fin p → List (Op r k) → Fin p → Prop
  | nil (pc : Fin p) : Contains M bad pc [] pc
  | cons {pc next stop op ops}
      (head : M.code pc = (Op.emit next bad op).resize w)
      (tail : Contains M bad next ops stop) : Contains M bad pc (op :: ops) stop

private theorem execute_reject (M : Machine w p r k) (c : Config w p r) (mem : Memory w)
    (bits : List Bool) (f : ℕ) (hb : M.code c.pc = .reject) :
    execute M.program f c mem bits = none := by
  cases f <;> simp [execute, Machine.program, hb, Instr.run]

private theorem program_step (M : Machine w p r k) (c : Config w p r) :
    M.program.step c = (M.code c.pc).run M.publicData c := rfl

/-- Native execution consumes one instruction of fuel per line and agrees
with the block semantics on registers, external memory and every event. -/
theorem Contains.execute {M : Machine w p r k} {bad start stop : Fin p} {ops : List (Op r k)}
    (h : Contains M bad start ops stop) (hb : M.code bad = .reject)
    (state : Word w) (regs : Regs w r) (priv : Word w → Word w)
    (mem : Memory w) (bits : List Bool) (f : ℕ) :
    BurstRAM.execute M.program (f + ops.length) ⟨start, state, regs, priv⟩ mem bits =
      run ops M.publicData state
        (fun regs mem ↦ BurstRAM.execute M.program f ⟨stop, state, regs, priv⟩ mem bits) regs mem := by
  induction h generalizing regs mem with
  | nil => rfl
  | @cons pc next stop op ops hhead htail ih =>
    have hre : BurstRAM.execute M.program (f + ops.length) ⟨bad, state, regs, priv⟩ mem bits = none :=
      execute_reject _ _ _ _ _ hb
    cases op <;>
      simp only [List.length_cons, BurstRAM.execute, program_step, hhead,
        Op.emit, Instr.resize, Instr.run, Config.put, run, List.foldr_cons, Op.run, Op.effect, Option.bind_some]
    all_goals first | exact congrArg (fun z => Option.map _ z) (ih _ _) | split <;> simp_all [run]

/-- Compile a whole block into a fixed table with a return and a reject instruction. -/
def template (ops : List (Op r k)) (result : Fin r) : Template (ops.length + 2) r k where
  literalWidth := 2
  entry := ⟨0, by omega⟩
  code i := if hi : i.val < ops.length then
      (ops[i.val]).emit ⟨i.val + 1, by omega⟩ ⟨ops.length + 1, by omega⟩
    else if i.val = ops.length then .returnState result else .reject

private theorem contains_indexed (M : Machine w p r k) (bad : Fin p) (ops : List (Op r k))
    (pc : Fin (ops.length+1) → Fin p)
    (hc : ∀ i : Fin ops.length, M.code (pc i.castSucc) =
      (Op.emit (pc i.succ) bad ops[i.val]).resize w) :
    Contains M bad (pc 0) ops (pc (Fin.last ops.length)) := by
  induction ops with
  | nil => exact .nil _
  | cons o ops ih =>
    apply Contains.cons (next := pc (⟨0, by simp⟩ : Fin (o :: ops).length).succ) (hc ⟨0, by simp⟩)
    exact ih (fun i => pc i.succ) (fun i => hc i.succ)

/-- The compiler places the complete block before its two terminal instructions. -/
theorem template_contains (ops : List (Op r k)) (result : Fin r) (pub : Fin k → Word w) :
    Contains ((template ops result).instantiate w pub) ⟨ops.length + 1, by omega⟩
      ⟨0, by omega⟩ ops ⟨ops.length, by omega⟩ := by
  apply contains_indexed _ _ ops (fun i => ⟨i.val, by have := i.isLt; omega⟩)
  intro i
  simp [template, Template.instantiate, i.isLt]

/-- Start at the entry of the actual opcode table. Registers may be supplied
by a preceding part of the same call. A standalone call supplies all zeros. -/
theorem execute_template (ops : List (Op r k)) (result : Fin r) (pub : Fin k → Word w)
    (state : Word w) (regs : Regs w r) (priv : Word w → Word w) (mem : Memory w) :
    let M := (template ops result).instantiate w pub
    BurstRAM.execute M.program (1 + ops.length) ⟨M.entry, state, regs, priv⟩ mem [] =
      run ops pub state (fun rs _ => some ⟨[], some (rs result)⟩) regs mem := by
  let M := (template ops result).instantiate w pub
  have hb : M.code ⟨ops.length + 1, by omega⟩ = .reject := by
    simp [M, template, Template.instantiate, Instr.resize, show ¬ops.length+1 < ops.length by omega]
  have he := (template_contains ops result pub).execute hb state regs priv mem [] 1
  have hret : M.code ⟨ops.length, by omega⟩ = .returnState result := by
    simp [M, template, Template.instantiate, Instr.resize]
  change _ = run ops M.publicData state _ regs mem
  apply he.trans
  congr 1
  funext rs m
  change BurstRAM.execute M.program 1 ⟨_, state, rs, priv⟩ m [] = _
  simp [BurstRAM.execute, program_step, hret, Instr.run]

end PrimedStackRAM

end VPVNP
end Computability
end OAI
