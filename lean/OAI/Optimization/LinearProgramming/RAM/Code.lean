import OAI.Optimization.LinearProgramming.RAM.Execution
import Lean.Elab.Tactic.Omega

/-! A small assembler for structured RAM programs. The semantics charges every compiled
instruction, including the jump back to a loop guard. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

variable {K : Type*}

structure Memory (K : Type*) where
  data : Nat → K
  index : Nat → Nat

def State.memory (s : State K) : Memory K := ⟨s.data, s.index⟩
def Memory.atPC (m : Memory K) (pc : Nat) : State K := ⟨pc, m.data, m.index, none⟩

def Memory.putData (m : Memory K) (dst : Nat) (x : K) : Memory K :=
  {m with data := Function.update m.data dst x}

def Memory.putIndex (m : Memory K) (dst x : Nat) : Memory K :=
  {m with index := Function.update m.index dst x}

inductive Cond where
  | scalarLT (left right : Nat)
  | addrLT (left right : Nat)
  deriving Repr

def Cond.test [LT K] [DecidableLT K] (c : Cond) (m : Memory K) : Bool :=
  match c with
  | .scalarLT a b => decide (m.data a < m.data b)
  | .addrLT a b => decide (m.index a < m.index b)

def Cond.instr (c : Cond) (yes no : Nat) : Instr :=
  match c with
  | .scalarLT a b => .branchLT a b yes no
  | .addrLT a b => .branchAddrLT a b yes no

inductive Block where
  | skip
  | op (i : Instr)
  | seq (first next : Block)
  | branch (cond : Cond) (yes no : Block)
  | loop (cond : Cond) (body : Block)
  deriving Repr

namespace Block

def size : Block → Nat
  | .skip => 0
  | .op _ => 1
  | .seq a b => a.size + b.size
  | .branch _ a b => 1 + a.size + 1 + b.size
  | .loop _ a => 1 + a.size + 1

/-- The argument `pc` is fixed at assembly time. Emitted code contains only machine
instructions with ordinary absolute addresses. -/
def compile : Block → Nat → List Instr
  | .skip, _ => []
  | .op i, _ => [i]
  | .seq a b, pc => a.compile pc ++ b.compile (pc + a.size)
  | .branch cond a b, pc =>
    let no := pc + 1 + a.size + 1
    [cond.instr (pc + 1) no] ++ a.compile (pc + 1) ++ [.jump (no + b.size)] ++ b.compile no
  | .loop cond a, pc =>
    [cond.instr (pc + 1) (pc + 1 + a.size + 1)] ++ a.compile (pc + 1) ++ [.jump pc]

@[simp] theorem length_compile (b : Block) (pc : Nat) : (b.compile pc).length = b.size := by
  induction b generalizing pc <;> simp_all [compile, size, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

inductive Eval (safe : Memory K → Prop) : Block → Memory K → Nat → Memory K → Prop where
  | skip {m} : safe m → Eval safe .skip m 0 m
  | op {i m n} : safe m → safe n →
      (∀ pc, execInstr i (m.atPC pc) = some (n.atPC (pc+1))) → Eval safe (.op i) m 1 n
  | seq {a b m n z k l} : Eval safe a m k n → Eval safe b n l z → Eval safe (.seq a b) m (k+l) z
  | branchTrue {c a b m z k} : c.test m = true → Eval safe a m k z →
      Eval safe (.branch c a b) m (1+k+1) z
  | branchFalse {c a b m z k} : c.test m = false → Eval safe b m k z →
      Eval safe (.branch c a b) m (1+k) z
  | loopFalse {c body m} : c.test m = false → safe m → Eval safe (.loop c body) m 1 m
  | loopTrue {c body m n z k l} : c.test m = true → Eval safe body m k n →
      Eval safe (.loop c body) n l z → Eval safe (.loop c body) m (1+k+1+l) z

namespace Eval

variable {safe : Memory K → Prop} {b : Block} {m n : Memory K} {k : Nat}

theorem safe_start (h : Eval safe b m k n) : safe m := by induction h <;> assumption

theorem safe_end (h : Eval safe b m k n) : safe n := by induction h <;> assumption

private theorem cond_exec (c : Cond) (m : Memory K) (pc yes no : Nat) :
    execInstr (c.instr yes no) (m.atPC pc) = some (m.atPC (if c.test m then yes else no)) := by
  cases c with
  | scalarLT a b =>
    by_cases h : m.data a < m.data b <;> simp [Cond.instr, Cond.test, execInstr, Memory.atPC, h]
  | addrLT a b =>
    by_cases h : m.index a < m.index b <;> simp [Cond.instr, Cond.test, execInstr, Memory.atPC, h]

theorem jump_exec (p : Program) (pc dst : Nat) (m : Memory K) (hs : safe m)
    (hi : p[pc]? = some (.jump dst)) :
    Execution p (fun s => safe s.memory) (m.atPC pc) 1 (m.atPC dst) := by
  exact .one hs (by simp [step, Memory.atPC, hi, execInstr]) hs

theorem test_exec (p : Program) (c : Cond) (m : Memory K) (pc yes no : Nat)
    (hs : safe m) (hi : p[pc]? = some (c.instr yes no)) :
    Execution p (fun s => safe s.memory) (m.atPC pc) 1
      (m.atPC (if c.test m then yes else no)) := by
  apply Execution.one hs _ hs
  change (match (none : Option Nat), p[pc]? with
    | none, some i => execInstr i (m.atPC pc)
    | _, _ => none) = _
  rw [hi]
  exact cond_exec _ _ _ _ _

theorem tail_at {p pc i xs} (h : CodeAt p pc (i :: xs)) : CodeAt p (pc+1) xs :=
  CodeAt.right (a := [i]) h

private theorem branch_parts {p pc c a b} (h : CodeAt p pc (compile (.branch c a b) pc)) :
    let no := pc + 1 + a.size + 1
    p[pc]? = some (c.instr (pc+1) no) ∧ CodeAt p (pc+1) (a.compile (pc+1)) ∧
    p[pc+1+a.size]? = some (.jump (no+b.size)) ∧ CodeAt p no (b.compile no) := by
  let no := pc + 1 + a.size + 1
  have whole : CodeAt p pc (c.instr (pc+1) no ::
      (a.compile (pc+1) ++ (.jump (no+b.size) :: b.compile no))) := by
    simpa [compile, no, List.append_assoc] using h
  have right := (tail_at whole).right
  rw [length_compile] at right
  exact ⟨whole.head, (tail_at whole).left, right.head, tail_at right⟩

private theorem loop_parts {p pc c a} (h : CodeAt p pc (compile (.loop c a) pc)) :
    p[pc]? = some (c.instr (pc+1) (pc+1+a.size+1)) ∧
    CodeAt p (pc+1) (a.compile (pc+1)) ∧ p[pc+1+a.size]? = some (.jump pc) := by
  have whole : CodeAt p pc (c.instr (pc+1) (pc+1+a.size+1) ::
      (a.compile (pc+1) ++ [.jump pc])) := by
    simpa [compile, List.append_assoc] using h
  have right := (tail_at whole).right
  rw [length_compile] at right
  exact ⟨whole.head, (tail_at whole).left, right.head⟩

/-- Every step in the structured derivation occurs in the assembled finite program. This
also transports the prescribed register invariant, and works at any code address. -/
theorem compile_correct {p : Program} {pc : Nat} (h : Eval safe b m k n)
    (code : CodeAt p pc (b.compile pc)) :
    Execution p (fun s => safe s.memory) (m.atPC pc) k (n.atPC (pc+b.size)) := by
  induction h generalizing pc with
  | skip hs => exact .done _ hs
  | op hs hn effect =>
    have hi := code.head
    apply Execution.one hs _ hn
    change (match (none : Option Nat), p[pc]? with
      | none, some i => execInstr i _
      | _, _ => none) = _
    rw [hi]
    exact effect pc
  | @seq a b m n z k l ea eb ia ib =>
    have left := ia code.left
    have right := code.right
    rw [length_compile] at right
    simpa [size, Nat.add_assoc] using left.append (ib right)
  | @branchTrue c a b m z k ht ea ia =>
    obtain ⟨hi, hyes, hj, _⟩ := branch_parts code
    have first := test_exec p c m pc _ _ ea.safe_start hi
    simp [ht] at first
    have middle := ia hyes
    have last := jump_exec p _ _ z ea.safe_end hj
    simpa [size, Nat.add_assoc] using (first.append middle).append last
  | @branchFalse c a b m z k ht eb ib =>
    obtain ⟨hi, _, _, hno⟩ := branch_parts code
    have first := test_exec p c m pc _ _ eb.safe_start hi
    simp [ht] at first
    simpa [size, Nat.add_assoc] using first.append (ib hno)
  | @loopFalse c a m ht hs =>
    obtain ⟨hi, _, _⟩ := loop_parts code
    simpa [ht, size, Nat.add_assoc] using test_exec p c m pc _ _ hs hi
  | @loopTrue c a m n z k l ht ea el ia il =>
    obtain ⟨hi, ha, hj⟩ := loop_parts code
    have first := test_exec p c m pc _ _ ea.safe_start hi
    simp [ht] at first
    have body := ia ha
    have back := jump_exec p _ _ n ea.safe_end hj
    exact ((first.append body).append back).append (il code)

/-- Assemble the block followed by a return instruction. The resulting halted trace has
exactly one more step than the block derivation. -/
theorem halted_trace {tag : Nat} (h : Eval safe b m k n) :
    let p := b.compile 0 ++ [.halt tag]
    ∃ t : Fin ((k+1)+1) → State K, Trace p (m.atPC 0) (k+1) t ∧
      (t (Fin.last (k+1))).output = some tag ∧ (t (Fin.last (k+1))).memory = n ∧
      ∀ i, safe (t i).memory := by
  let p := b.compile 0 ++ [.halt tag]
  have whole : CodeAt p 0 (b.compile 0 ++ [.halt tag]) := CodeAt.whole _
  have code := h.compile_correct whole.left
  have stop := whole.right.head
  rw [length_compile, Nat.zero_add] at stop
  let last : State K := {n.atPC (0+b.size) with output := some tag}
  have finish : Execution p (fun s => safe s.memory) (n.atPC (0+b.size)) 1 last :=
    .one h.safe_end (by simp [step, Memory.atPC, stop, execInstr, last]) h.safe_end
  obtain ⟨t, ht, hend, hsafe⟩ := (code.append finish).to_trace
  exact ⟨t, ht, hend ▸ rfl, hend ▸ rfl, hsafe⟩

end Eval
end Block
end RAM
end LinearProgramming
end Optimization
end OAI
