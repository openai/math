import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.OracleSpec.Machine
import Lean.Elab.Tactic.Omega

/-! Literal RAM dispatch for finite bit programs. Every ordinal comparison is charged. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open RAM OracleSpec

def select (key scratch base : ℕ) : List Block → Block
  | [] => .skip
  | b :: bs => .seq (.op (.addrConst scratch (base+1)))
      (.branch (.addrLT key scratch) b (select key scratch (base+1) bs))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem setIndex {safe : RAM.Memory K → Prop} {m : RAM.Memory K} {s v : ℕ}
    (hm : safe m) (hn : safe (m.putIndex s v)) :
    Block.Eval safe (.op (.addrConst s v)) m 1 (m.putIndex s v) :=
  .op hm hn (fun _ => rfl)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem overwrite (m : RAM.Memory K) (s u v : ℕ) :
    (m.putIndex s u).putIndex s v = m.putIndex s v := by simp [RAM.Memory.putIndex]

/-- Exact finite-table overhead, including the final jump around the other alternatives. -/
theorem select_eval {safe : RAM.Memory K → Prop} (key scratch : ℕ) (hdis : key ≠ scratch)
    (rows : List Block) (base i : ℕ) (hi : i < rows.length) {m out : RAM.Memory K} {time : ℕ}
    (hm : safe m) (hs : ∀ x, safe (m.putIndex scratch x)) (hk : m.index key = base+i)
    (run : Block.Eval safe rows[i] (m.putIndex scratch (base+i+1)) time out) :
    Block.Eval safe (select key scratch base rows) m (2*i+3+time) out := by
  induction rows generalizing base i m with
  | nil => simp at hi
  | cons b bs ih =>
    let t := m.putIndex scratch (base+1)
    have hset : Block.Eval safe (.op (.addrConst scratch (base+1))) m 1 t := setIndex hm (hs _)
    cases i with
    | zero =>
      have htest : (Cond.addrLT key scratch).test t = true := by simp [Cond.test, t, hdis, hk]
      have body : Block.Eval safe b t time out := run
      have both := Block.Eval.seq hset (Block.Eval.branchTrue (b := select key scratch (base+1) bs) htest body)
      simpa only [select, Nat.mul_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using both
    | succ i =>
      have hi' : i < bs.length := by simpa using hi
      have htest : (Cond.addrLT key scratch).test t = false := by simp [Cond.test, t, hdis, hk]
      have hk' : t.index key = base+1+i := by simp [t, hdis, hk]; omega
      have body : Block.Eval safe bs[i] (t.putIndex scratch (base+1+i+1)) time out := by
        simpa [t, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run
      have rest := ih (base+1) i hi' (by exact hs _) (by intro v; simpa [t] using hs v) hk' body
      have both := Block.Eval.seq hset (Block.Eval.branchFalse (a := b) htest rest)
      rw [show 2*(i+1)+3+time = 1+(1+(2*i+3+time)) by omega]
      exact both

def tagIndex : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

def tags (f : Option Bool → Block) := [f none, f (some false), f (some true)]

private theorem tags_at (f : Option Bool → Block) (b : Option Bool) :
    (tags f)[(tagIndex b).val]'((tagIndex b).isLt) = f b := by
  cases b with
  | none => rfl
  | some b => cases b <;> rfl

/-- Unshared even scratch address for testing a finite row or an observed symbol. -/
def thresholdReg := 24

def row (p : BitProgram) (peek : Fin p.stackCount → Block)
    (action : BitInstruction (Fin p.states) (Fin p.stackCount) → Block) (q : Fin p.states) : Block :=
  .seq (peek (p.scan q)) (select 0 thresholdReg 0 (tags (fun b => action (p.instruction q b))))

def table (p : BitProgram) (peek : Fin p.stackCount → Block)
    (action : BitInstruction (Fin p.states) (Fin p.stackCount) → Block) : Block :=
  select 39 thresholdReg 0 (List.ofFn (row p peek action))

/-- For one entire finite program, the concrete table calls exactly the selected peek and
instruction in both branches of its decision tree. -/
theorem table_eval {safe : RAM.Memory K → Prop} (p : BitProgram) (peek : Fin p.stackCount → Block)
    (action : BitInstruction (Fin p.states) (Fin p.stackCount) → Block) (q : Fin p.states)
    (bit : Option Bool) {m mid out : RAM.Memory K} {peekCost actionCost : ℕ}
    (hm : safe m) (hms : ∀ v, safe (m.putIndex thresholdReg v)) (hq : m.index 39 = q.val)
    (peeks : Block.Eval safe (peek (p.scan q)) (m.putIndex thresholdReg (q.val+1)) peekCost mid)
    (hmid : ∀ v, safe (mid.putIndex thresholdReg v)) (hb : mid.index 0 = (tagIndex bit).val)
    (runs : Block.Eval safe (action (p.instruction q bit))
      (mid.putIndex thresholdReg ((tagIndex bit).val+1)) actionCost out) :
    Block.Eval safe (table p peek action) m
      (2*q.val+3+(peekCost+(2*(tagIndex bit).val+3+actionCost))) out := by
  let choices := tags (fun b => action (p.instruction q b))
  have ht : (tagIndex bit).val < choices.length := (tagIndex bit).isLt
  have chosen := select_eval 0 thresholdReg (by decide) choices 0 (tagIndex bit).val ht
    peeks.safe_end hmid (by simpa only [Nat.zero_add] using hb)
    (by cases bit with
        | none => exact runs
        | some b => cases b <;> exact runs)
  let rows := List.ofFn (row p peek action)
  have hq' : q.val < rows.length := by simpa only [rows, List.length_ofFn] using q.isLt
  have both := Block.Eval.seq peeks chosen
  exact select_eval 39 thresholdReg (by decide) rows 0 q.val hq' hm hms
    (by simpa only [Nat.zero_add] using hq)
    (by simpa only [rows, List.getElem_ofFn, Nat.zero_add, row, choices] using both)

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
