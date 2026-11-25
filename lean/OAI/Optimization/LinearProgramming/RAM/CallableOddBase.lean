import OAI.Optimization.LinearProgramming.RAM.CallMemory
import OAI.Optimization.LinearProgramming.RAM.Array

/-! The caller's odd scalar and address registers both use translated addresses.
The even register bank, including the callee's encoded addresses, is untouched. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Odd

variable {K : Type*}

def slot (i : ℕ) : ℕ := 2*i+1

def frame (caller : Memory K) : Memory K := ⟨caller.data, fun i => slot (caller.index i)⟩

def memory (callee caller : Memory K) : Memory K := Call.pack callee (frame caller)

@[simp] theorem data_slot (callee caller : Memory K) (i : ℕ) :
    (memory callee caller).data (slot i) = caller.data i := by simp [memory,slot,frame]

@[simp] theorem index_slot (callee caller : Memory K) (i : ℕ) :
    (memory callee caller).index (slot i) = slot (caller.index i) := by simp [memory,slot,frame]

@[simp] theorem data_even (callee caller : Memory K) (i : ℕ) :
    (memory callee caller).data (2*i) = callee.data i := by simp [memory]

@[simp] theorem index_even (callee caller : Memory K) (i : ℕ) :
    (memory callee caller).index (2*i) = 2*callee.index i := by simp [memory]

@[simp] theorem even_ne_slot (i j : ℕ) : 2*i ≠ slot j := by dsimp [slot]; omega

@[simp] theorem slot_inj {i j : ℕ} : slot i = slot j ↔ i=j := by dsimp [slot]; omega

@[simp] theorem slot_lt {i j : ℕ} : slot i < slot j ↔ i<j := by dsimp [slot]; omega

private theorem memory_ext {m n : Memory K} (hd : ∀j, m.data j = n.data j)
    (hi : ∀j, m.index j = n.index j) : m=n := by
  cases m; cases n
  congr <;> funext j
  · exact hd j
  · exact hi j

private theorem cases_address (T : ℕ → Prop) (he : ∀j, T (2*j)) (ho : ∀j, T (slot j))
    (i : ℕ) : T i := by
  by_cases h : i%2=0
  · exact (show 2*(i/2)=i by omega) ▸ he (i/2)
  · exact (show slot (i/2)=i by dsimp [slot]; omega) ▸ ho (i/2)

@[simp] theorem putData (callee caller : Memory K) (i : ℕ) (x : K) :
    (memory callee caller).putData (slot i) x = memory callee (caller.putData i x) := by
  apply memory_ext
  · apply cases_address
    · intro j
      simp [Memory.putData]
    · intro j
      by_cases h : j = i
      · subst j; simp [Memory.putData]
      · have h' : slot j ≠ slot i := fun he => h (slot_inj.mp he)
        simp [Memory.putData,Function.update_of_ne,h,h']
  · apply cases_address <;> intro j <;> simp [Memory.putData]

@[simp] theorem putIndex (callee caller : Memory K) (i v : ℕ) :
    (memory callee caller).putIndex (slot i) (slot v) = memory callee (caller.putIndex i v) := by
  apply memory_ext
  · apply cases_address <;> intro j <;> simp [Memory.putIndex]
  · apply cases_address
    · intro j
      simp [Memory.putIndex]
    · intro j
      by_cases h : j=i
      · subst j; simp [Memory.putIndex]
      · have h' : slot j ≠ slot i := fun he => h (slot_inj.mp he)
        simp [Memory.putIndex,Function.update_of_ne,h,h']

theorem allData {P : K → Prop} (callee caller : Memory K)
    (hc : callee.AllData P) (hm : caller.AllData P) : (memory callee caller).AllData P :=
  cases_address _ (fun j => by simpa using hc j) (fun j => by simpa using hm j)

def cond : Cond → Cond
  | .scalarLT a b => .scalarLT (slot a) (slot b)
  | .addrLT a b => .addrLT (slot a) (slot b)

@[simp] theorem cond_test [LT K] [DecidableLT K] (c : Cond) (callee caller : Memory K) :
    (cond c).test (memory callee caller) = c.test caller := by
  cases c <;> simp [cond,Cond.test]

/-- The four control-flow instructions cannot occur as a falling-through primitive
at every program counter; structured control is compiled separately. -/
def instr : Instr → Block
  | .const d q => .op (.const (slot d) q)
  | .copy d a => .op (.copy (slot d) (slot a))
  | .add d a b => .op (.add (slot d) (slot a) (slot b))
  | .sub d a b => .op (.sub (slot d) (slot a) (slot b))
  | .mul d a b => .op (.mul (slot d) (slot a) (slot b))
  | .div d a b => .op (.div (slot d) (slot a) (slot b))
  | .load d a => .op (.load (slot d) (slot a))
  | .store a d => .op (.store (slot a) (slot d))
  | .addrConst d n => .op (.addrConst (slot d) (slot n))
  | .addrCopy d a => .op (.addrCopy (slot d) (slot a))
  | .incr d a => Block.straight [.incr (slot d) (slot a), .incr (slot d) (slot d)]
  | .decr d a => Block.straight [.decr (slot d) (slot a), .decr (slot d) (slot d),
      .decr (slot d) (slot d), .incr (slot d) (slot d)]
  | .addrLoad d a => .op (.addrLoad (slot d) (slot a))
  | .addrStore a d => .op (.addrStore (slot a) (slot d))
  | .branchLT .. | .branchAddrLT .. | .jump .. | .halt .. => .skip

def instrCost : Instr → ℕ
  | .incr .. => 2
  | .decr .. => 4
  | .branchLT .. | .branchAddrLT .. | .jump .. | .halt .. => 0
  | _ => 1

theorem instrCost_le (i : Instr) : instrCost i ≤ 4 := by cases i <;> norm_num [instrCost]

end Odd
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
