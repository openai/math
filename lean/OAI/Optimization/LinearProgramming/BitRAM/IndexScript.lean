import OAI.Optimization.LinearProgramming.RAM.RAMCount
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Straight-line evaluation of actual address-only RAM instructions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace IndexScript

open RAM RAM.Block RAM.Tape

def allowed : Instr → Bool
  | .addrConst .. | .addrCopy .. | .incr .. | .decr .. | .addrLoad .. | .addrStore .. => true
  | _ => false

def update (a : Nat → Nat) : Instr → Nat → Nat
  | .addrConst i v => Function.update a i v
  | .addrCopy i j => Function.update a i (a j)
  | .incr i j => Function.update a i (a j+1)
  | .decr i j => Function.update a i (a j-1)
  | .addrLoad i j => Function.update a i (a (a j))
  | .addrStore i j => Function.update a (a i) (a j)
  | _ => a

def run : List Instr → (Nat → Nat) → Nat → Nat
  | [], a => a
  | i::rest, a => run rest (update a i)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem one (i : Instr) (ok : allowed i = true) (s : Memory K) {P : K → Prop} (hs : Good P s) :
    Eval (Good P) (.op i) s 1 ⟨s.data,update s.index i⟩ := by
  cases i <;> first | exact .op hs hs (fun _ => rfl) | contradiction

theorem correct (code : List Instr) (ok : ∀ i ∈ code, allowed i = true)
    (s : Memory K) {P : K → Prop} (hs : Good P s) :
    Eval (Good P) (.straight code) s code.length ⟨s.data,run code s.index⟩ := by
  induction code generalizing s with
  | nil => exact .skip hs
  | cons i is ih =>
    have h := one i (ok i (by simp)) s hs
    have h' := ih (fun j hj => ok j (List.mem_cons_of_mem _ hj)) ⟨s.data,update s.index i⟩ h.safe_end
    simpa only [run,Block.straight,List.length_cons,Nat.add_comm 1] using h.seq h'

end IndexScript
end BitRAM
end LinearProgramming
end Optimization
end OAI
