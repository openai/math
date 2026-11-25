import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.RAM.CallableInvoke
import OAI.Optimization.LinearProgramming.RAM.Footprint

/-! Bounds on memory operands of relocatable fragments. Program counters and return tags
have their own types of use in the instruction dispatcher and never enter the memory bank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

/-- Direct data/index registers and address literals of a single instruction. -/
def Instr.accessBudget : Instr → ℕ
  | .branchLT a b _ _ | .branchAddrLT a b _ _ => a+b
  | .jump _ | .halt _ => 0
  | i => i.addressBudget

def Cond.accessBudget : Cond → ℕ
  | .scalarLT a b | .addrLT a b => a+b

@[simp] theorem Cond.instr_accessBudget (c : Cond) (y n : ℕ) : (c.instr y n).accessBudget = c.accessBudget := by
  cases c <;> rfl

/-- A block's exact list of memory-operand bounds before its program counters are placed. -/
def Block.accessWords : Block → List ℕ
  | .skip => []
  | .op i => [i.accessBudget]
  | .seq a b => a.accessWords++b.accessWords
  | .branch c a b => c.accessBudget::(a.accessWords++0::b.accessWords)
  | .loop c a => c.accessBudget::(a.accessWords++[0])

theorem Block.compile_accessWords (b : Block) (pc : ℕ) :
    (b.compile pc).map Instr.accessBudget=b.accessWords := by
  induction b generalizing pc <;> simp_all [Block.compile,Block.accessWords,List.append_assoc,Instr.accessBudget]
  all_goals exact Cond.instr_accessBudget _ _ _

namespace Callable.Fragment

/-- This bound is uniform in the code placement and covers every emitted instruction. -/
def Scoped (f : Fragment) (budget : ℕ) := ∀ pc i, i∈f.emit pc → i.accessBudget≤budget

/-- The emitted memory operands are independent of the instruction's absolute code location. -/
class FixedAccess (f : Fragment) : Prop where
  words : ∀ pc, (f.emit pc).map Instr.accessBudget = (f.emit 0).map Instr.accessBudget

/-- A computable constant from the fragment alone, without its caller or installation site. -/
def localBudget (f : Fragment) := ((f.emit 0).map Instr.accessBudget).sum

theorem scoped_localBudget (f : Fragment) [FixedAccess f] : f.Scoped f.localBudget := by
  intro pc i hi
  have h := List.le_sum_of_mem (List.mem_map.mpr ⟨i,hi,rfl⟩ : i.accessBudget∈(f.emit pc).map Instr.accessBudget)
  rwa [FixedAccess.words (f:=f) pc] at h

theorem Scoped.mono {f : Fragment} {a b : ℕ} (h : f.Scoped a) (hab : a≤b) : f.Scoped b :=
  fun pc i hi => (h pc i hi).trans hab

private theorem FixedAccess.fromWords {f : Fragment} (ws : List ℕ)
    (eqn : ∀ pc,(f.emit pc).map Instr.accessBudget=ws) : FixedAccess f :=
  ⟨fun pc => (eqn pc).trans (eqn 0).symm⟩

instance (b : Block) : FixedAccess (ofBlock b) := FixedAccess.fromWords b.accessWords b.compile_accessWords

instance (a b : Fragment) [FixedAccess a] [FixedAccess b] : FixedAccess (seq a b) := by
  apply FixedAccess.fromWords ((a.emit 0).map Instr.accessBudget ++ (b.emit 0).map Instr.accessBudget)
  intro pc
  simp only [seq,List.map_append]
  rw [FixedAccess.words (f:=a) pc,FixedAccess.words (f:=b) (pc+a.size)]

instance (c : Cond) (a b : Fragment) [FixedAccess a] [FixedAccess b] : FixedAccess (branch c a b) := by
  apply FixedAccess.fromWords (c.accessBudget::((a.emit 0).map Instr.accessBudget++0::(b.emit 0).map Instr.accessBudget))
  intro pc
  simp only [branch,List.map_cons,List.map_append,Cond.instr_accessBudget]
  rw [FixedAccess.words (f:=a) (pc+1),FixedAccess.words (f:=b) (pc+1+a.size+1)]
  rfl

instance (c : Cond) (a : Fragment) [FixedAccess a] : FixedAccess (loop c a) := by
  apply FixedAccess.fromWords (c.accessBudget::((a.emit 0).map Instr.accessBudget++[0]))
  intro pc
  simp only [loop,List.map_cons,List.map_append,List.map_nil,Cond.instr_accessBudget]
  rw [FixedAccess.words (f:=a) (pc+1)]
  rfl

instance (i n : ℕ) (body : Fragment) [FixedAccess body] : FixedAccess (forRange i n body) := by
  unfold forRange
  infer_instance

private theorem native_words (p : Program) (ret addr : ℕ→ℕ) :
    (p.flatMap (Call.emit ret addr)).map Instr.accessBudget =
      (p.flatMap (Call.emit (fun _ => 0) (fun _ => 0))).map Instr.accessBudget := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.flatMap_cons,List.map_append,ih]
    congr 1
    cases i <;> rfl

private theorem return_words (sink : TagSink) (count endPC : ℕ) :
    (tagTable sink count endPC).map Instr.accessBudget = (tagTable sink count 0).map Instr.accessBudget := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [tagTable_succ,List.map_append,ih]; rfl

instance (p : Program) (count : ℕ) (sink : TagSink) : FixedAccess (invoke p count sink) := by
  apply FixedAccess.fromWords ((p.flatMap (Call.emit (fun _ => 0) (fun _ => 0))).map Instr.accessBudget ++
    (tagTable sink count 0).map Instr.accessBudget)
  intro pc
  simp only [invoke,Call.subroutine,Layout.assemble,List.map_append]
  exact congrArg₂ List.append (native_words p _ _) (return_words sink count _)

end Callable.Fragment
end RAM
end LinearProgramming
end Optimization
end OAI
