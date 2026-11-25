import OAI.Optimization.LinearProgramming.BitRAM.DispatchLoop
import OAI.Optimization.LinearProgramming.BitRAM.Ops
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf
import OAI.Optimization.LinearProgramming.RAM.CallableControl

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG
open RAM RAM.Tape RAM.Callable OracleSpec BitRAM

/-- The status lives in the bit interpreter's private bank. A real restart installs
the halt sentinel before another numerical request can be served. -/
def finishCode (p : BitProgram) (status : ℕ) : Block :=
  .seq (.branch (.addrLT nilReg status) (.op (.addrConst stateReg p.states)) .skip)
    (.op (.addrConst Dispatch.limitReg p.states))

def epochGuard : Cond := Odd.cond (.addrLT stateReg Dispatch.limitReg)

def framedLoop (p : BitProgram) (status : ℕ) (boundary : Fragment) : Fragment :=
  .seq (Odd.leaf (.op (.addrConst Dispatch.limitReg p.states)))
    (.loop epochGuard (.seq boundary (Odd.leaf (finishCode p status))))

def boundaryCost (p : BitProgram) (budget n : ℕ) := 4*((2*p.states+35)*(n+1)+2)+budget+2

def epochUnit (p : BitProgram) (budget : ℕ) := 4*(2*p.states+35)+budget+32

theorem boundaryCost_le (p : BitProgram) (budget n : ℕ) :
    1+(boundaryCost p budget n+16)+1 ≤ epochUnit p budget*(n+1) := by
  let a := 2*p.states+35
  have norm : 4*(a*(n+1)+2)=(4*a)*(n+1)+8 := by
    rw [Nat.mul_add 4 (a*(n+1)) 2,Nat.mul_assoc 4 a (n+1)]
  have pos := Nat.mul_le_mul_left (budget+32) (show 1 ≤ n+1 by omega)
  rw [Nat.mul_one] at pos
  change 1+(4*(a*(n+1)+2)+budget+2+16)+1 ≤ (4*a+budget+32)*(n+1)
  rw [norm,show 4*a+budget+32=4*a+(budget+32) by omega,Nat.add_mul]
  omega

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem finish_answer {p : BitProgram} {P : K → Prop} (status : ℕ) {m native : Memory K}
    (safe : Good P m) (nativeSafe : native.AllData P) (nil : m.index nilReg=0)
    (flag : m.index status=0) :
    (Odd.leaf (finishCode p status)).Run P (Odd.memory native m) 16
      (Odd.memory native (m.putIndex Dispatch.limitReg p.states)) := by
  have test : (Cond.addrLT nilReg status).test m=false := by simp [Cond.test,nil,flag]
  have first : Block.Eval (Good P) (.branch (.addrLT nilReg status) (.op (.addrConst stateReg p.states)) .skip)
      m (1+0) m := .branchFalse test (.skip safe)
  exact (Odd.leaf_run P native nativeSafe (first.seq (eval_constI m safe Dispatch.limitReg p.states))).mono (by decide)

theorem finish_restart {p : BitProgram} {P : K → Prop} (status : ℕ) {m native : Memory K}
    (safe : Good P m) (nativeSafe : native.AllData P) (nil : m.index nilReg=0) (flag : 0<m.index status) :
    (Odd.leaf (finishCode p status)).Run P (Odd.memory native m) 16
      (Odd.memory native ((m.putIndex stateReg p.states).putIndex Dispatch.limitReg p.states)) := by
  have test : (Cond.addrLT nilReg status).test m=true := by simp [Cond.test,nil,flag]
  have first : Block.Eval (Good P) (.branch (.addrLT nilReg status) (.op (.addrConst stateReg p.states)) .skip)
      m (1+1+1) (m.putIndex stateReg p.states) := .branchTrue test (eval_constI m safe stateReg p.states)
  exact Odd.leaf_run P native nativeSafe (first.seq (eval_constI _ first.safe_end Dispatch.limitReg p.states))

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem ready_headers (m : Memory K) (n : ℕ) :
    ∀ i, 43 ≤ i → i < 65 → (m.putIndex Dispatch.limitReg n).index i=m.index i := by
  intro i low _
  exact Memory.putIndex_ne m (by unfold Dispatch.limitReg;omega) n

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem paired_safe {P : K → Prop} {native m : Memory K} (h : (Odd.memory native m).AllData P) :
    native.AllData P ∧ m.AllData P :=
  ⟨fun i => by simpa only [Odd.data_even] using h (2*i),
    fun i => by simpa only [Odd.data_slot] using h (Odd.slot i)⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
