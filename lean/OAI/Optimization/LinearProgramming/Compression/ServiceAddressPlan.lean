import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Straight-line address setup preserves the complete scalar bank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

variable {K : Type*}

open RAM

/-- The three address assignments used to set up pointers, constants, and range counters. -/
inductive AddressSet where
  | fix (dst value : ℕ)
  | read (dst src : ℕ)
  | next (dst src : ℕ)

def AddressSet.instr : AddressSet → Instr
  | .fix dst value => .addrConst dst value
  | .read dst src => .addrCopy dst src
  | .next dst src => .incr dst src

def AddressSet.apply (s : Memory K) : AddressSet → Memory K
  | .fix dst value => s.putIndex dst value
  | .read dst src => s.putIndex dst (s.index src)
  | .next dst src => s.putIndex dst (s.index src+1)

@[simp] theorem AddressSet.data (s : Memory K) (a : AddressSet) : (a.apply s).data=s.data := by cases a <;> rfl

def addressPlan (xs : List AddressSet) : Block := Block.straight (xs.map AddressSet.instr)

def applyPlan (xs : List AddressSet) (s : Memory K) : Memory K := xs.foldl AddressSet.apply s

@[simp] theorem applyPlan_data (xs : List AddressSet) (s : Memory K) : (applyPlan xs s).data=s.data := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => exact (ih (a.apply s)).trans (a.data s)

/-- Every fixed address assignment in the control code takes exactly one native instruction. -/
theorem addressPlan_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : (ℕ → K) → Prop) (xs : List AddressSet) (s : Memory K) (hs : P s.data) :
    Block.Eval (fun z => P z.data) (addressPlan xs) s xs.length (applyPlan xs s) := by
  induction xs generalizing s with
  | nil => exact .skip hs
  | cons a xs ih =>
    have ea : Block.Eval (fun z => P z.data) (.op a.instr) s 1 (a.apply s) := by
      cases a with
      | fix dst val => exact Block.Eval.op_addrConst _ _ _ hs hs
      | read dst src => exact Block.Eval.op_addrCopy _ _ _ hs hs
      | next dst src => exact Block.Eval.op_incr _ _ _ hs hs
    simpa [addressPlan,Block.straight,applyPlan,Nat.add_comm] using ea.seq (ih (a.apply s) (by simpa using hs))

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
