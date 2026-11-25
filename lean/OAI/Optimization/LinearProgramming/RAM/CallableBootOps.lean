import OAI.Optimization.LinearProgramming.RAM.Array

/-! Straight-line address instructions and the unary address encoding used at a
callable fragment's ordinary entry. Every address instruction preserves the scalar bank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

variable {K : Type*}

open Block

inductive AddressOp where
  | set (dst val : ℕ)
  | copy (dst src : ℕ)
  | incr (dst src : ℕ)
  | decr (dst src : ℕ)
  | load (dst ptr : ℕ)
  | store (ptr src : ℕ)

def AddressOp.instr : AddressOp → Instr
  | .set d n => .addrConst d n
  | .copy d r => .addrCopy d r
  | .incr d r => .incr d r
  | .decr d r => .decr d r
  | .load d a => .addrLoad d a
  | .store a r => .addrStore a r

def AddressOp.apply (s : Memory K) : AddressOp → Memory K
  | .set d n => s.putIndex d n
  | .copy d r => s.putIndex d (s.index r)
  | .incr d r => s.putIndex d (s.index r+1)
  | .decr d r => s.putIndex d (s.index r-1)
  | .load d a => s.putIndex d (s.index (s.index a))
  | .store a r => s.putIndex (s.index a) (s.index r)

def program (ops : List AddressOp) : Block := .straight (ops.map AddressOp.instr)
def applyOps (ops : List AddressOp) (s : Memory K) : Memory K := ops.foldl AddressOp.apply s

@[simp] theorem apply_data (s : Memory K) (a : AddressOp) : (a.apply s).data=s.data := by
  cases a <;> rfl

@[simp] theorem ops_data (ops : List AddressOp) (s : Memory K) : (applyOps ops s).data=s.data := by
  induction ops generalizing s with
  | nil => rfl
  | cons a ops ih => exact (ih (a.apply s)).trans (apply_data s a)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ops_spec (P : K → Prop) (ops : List AddressOp) (s : Memory K) (hs : s.AllData P) :
    Eval (Memory.AllData P) (program ops) s ops.length (applyOps ops s) := by
  induction ops generalizing s with
  | nil => exact .skip hs
  | cons a ops ih =>
    have step : Eval (Memory.AllData P) (.op a.instr) s 1 (a.apply s) := by
      cases a with
      | set d n => exact Eval.op_addrConst _ _ _ hs hs
      | copy d r => exact Eval.op_addrCopy _ _ _ hs hs
      | incr d r => exact Eval.op_incr _ _ _ hs hs
      | decr d r => exact Eval.op_decr _ _ _ hs hs
      | load d p => exact Eval.op_addrLoad _ _ _ hs hs
      | store p r => exact Eval.op_addrStore _ _ _ hs hs
    simpa [program,Block.straight,applyOps,Nat.add_comm] using step.seq (ih (a.apply s) step.safe_end)

/-- Store the odd-bank encoding of the address in register 9 into register 10.
Register 11 counts the charged unit increments. -/
def encodeBlock : Block := .seq (.op (.addrConst 10 1)) <|
  .forRange 11 9 (program [.incr 10 10,.incr 10 10])

theorem encode_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P) :
    ∃ t, Eval (Memory.AllData P) encodeBlock s (5*s.index 9+3) t ∧
      t.data=s.data ∧ t.index 10=2*s.index 9+1 ∧
      ∀ r, r≠10 → r≠11 → t.index r=s.index r := by
  let a := s.putIndex 10 1
  let I := fun (i : ℕ) (u : Memory K) => u.AllData P ∧
    u.index 11=i ∧ u.index 10=2*i+1 ∧ u.data=s.data ∧
    ∀ r, r≠10 → r≠11 → u.index r=s.index r
  have e := Eval.op_addrConst (safe:=Memory.AllData P) s 10 1 hs hs
  have init : I 0 (a.putIndex 11 0) := by
    refine ⟨hs,by simp,by simp [a],rfl,?_⟩
    intro r hr h11
    simp [a,hr,h11]
  obtain ⟨t,run,_,_,out,dat,frame⟩ := Eval.forRange_invariant_exact (safe:=Memory.AllData P)
    (body:=program [.incr 10 10,.incr 10 10]) 11 9 (s.index 9) 2 I a hs init
    (fun _ u h => ⟨h.1,h.2.1,h.2.2.2.2 9 (by decide) (by decide)⟩)
    (by
      intro i hi u h
      let v := applyOps [.incr 10 10,.incr 10 10] u
      have ev := ops_spec P [.incr 10 10,.incr 10 10] u h.1
      refine ⟨v,ev,ev.safe_end,?_,?_,h.2.2.2.1,?_⟩
      · simp [v,applyOps,AddressOp.apply,h.2.1]
      · simp [v,applyOps,AddressOp.apply,h.2.2.1]
        omega
      · intro r hr h11
        simpa [v,applyOps,AddressOp.apply,hr,h11] using h.2.2.2.2 r hr h11)
  refine ⟨t,?_,dat,out,frame⟩
  rw [show 5*s.index 9+3=1+(s.index 9*(2+3)+2) by omega]
  exact e.seq run

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
