import OAI.Optimization.LinearProgramming.RAM.Call
import OAI.Optimization.LinearProgramming.RAM.CallFrameView
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Binding a verified external scalar RAM program to the actual calling convention. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The callee starts with its canonical input on the even registers. Its return tag
selects an actual program counter of the caller. All odd caller data and address
registers survive, including original input and witnesses needed in later calls. -/
theorem invoke_prepared_trace {original target : Program} {ret : Nat → Nat} {base k tag : Nat}
    (physical : Memory K) (dims : List Nat) (input : List K) (P : K → Prop)
    (code : CodeAt target base (subroutine original base ret))
    (hdata : ∀ j, physical.data (2*j) = (start dims input).data j)
    (hindex : ∀ j, physical.index (2*j) = 2*(start dims input).index j)
    (hphysical : ∀ j, P (physical.data j)) (trace : Fin (k+1) → State K)
    (hrun : Trace original (start dims input) k trace)
    (hsafe : ∀ i j, P ((trace i).data j)) (hdone : (trace (Fin.last k)).output = some tag) :
    ∃ n ≤ 2*k, ∃ s : Memory K,
      Execution target (fun st => ∀ j, P (st.data j)) (physical.atPC base) n (s.atPC (ret tag)) ∧
      (∀ j, s.data (2*j) = (trace (Fin.last k)).data j) ∧
      (∀ j, s.index (2*j) = 2*(trace (Fin.last k)).index j) ∧
      (∀ j, s.data (2*j+1) = physical.data (2*j+1)) ∧
      (∀ j, s.index (2*j+1) = physical.index (2*j+1)) := by
  let frame := savedOddFrame physical
  let addr := Layout.addr original width base
  have hp : physical = pack (start dims input).memory frame :=
    eq_pack_of_even physical _ hdata hindex
  have safe (i : Fin (k+1)) : ∀ j, P ((pack (trace i).memory frame).data j) := by
    intro j
    simp only [pack]
    split
    · exact hsafe i _
    · exact hphysical _
  have startPC : image frame ret addr (start dims input) = physical.atPC base := by
    change (pack (start dims input).memory frame).atPC (addr 0) = _
    rw [← hp]
    simp [addr,Layout.addr]
  obtain ⟨n,hn,run⟩ := simulate_execution (good := fun data => ∀ j, P (data j)) code
    (Execution.of_trace hrun safe)
  let last := trace (Fin.last k)
  have donePC : image frame ret addr last = (pack last.memory frame).atPC (ret tag) := by
    simp [image, position, last, hdone]
  change Execution _ _ (image frame ret addr (start dims input)) _ (image frame ret addr last) at run
  rw [startPC,donePC] at run
  exact ⟨n,hn,pack last.memory frame,run,data_even _ _,index_even _ _,data_odd _ _,index_odd _ _⟩

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
