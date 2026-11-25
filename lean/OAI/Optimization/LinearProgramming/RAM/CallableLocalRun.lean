import OAI.Optimization.LinearProgramming.RAM.CallableBase
import OAI.Optimization.LinearProgramming.RAM.CallableLocal

/-! Compose a verified finite address-tape initializer with a relocatable program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

variable {K : Type*}

def trimMemory (cap : ℕ) (m : Memory K) : Memory K := ⟨m.data,fun j => if j≤cap then m.index j else 0⟩

theorem trimMemory_atPC (cap : ℕ) (m : Memory K) (pc : ℕ) :
    (trimMemory cap m).atPC pc=trimIndex cap (m.atPC pc) := rfl

/-- Transfer the complete counted execution inside any concrete containing ROM. Its
emitted block can be preceded by an ordinary finite initialization routine. -/
theorem Fragment.run_at_trim {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {f : Fragment} {P : K → Prop} {m t : Memory K} {bound cap b : ℕ}
    (run : f.Run P m bound t) (prog : Program) (pc : ℕ) (code : CodeAt prog pc (f.emit pc))
    (hp : addressBudget prog≤b) (hi : ∀ j,m.index j≤b) (hcap : b+bound≤cap) :
    ∃ l≤bound, Execution prog (fun s => ∀j,P (s.data j))
      ((trimMemory cap m).atPC pc) l ((trimMemory cap t).atPC (pc+f.size)) := by
  obtain ⟨l,hl,hr⟩ := run prog pc code
  obtain ⟨tr,ht,he,hs⟩ := hr.to_trace
  have raw := trace_trimIndex hp hi ht ((Nat.add_le_add_left hl b).trans hcap)
  have out := Execution.of_trace (safe := fun s => ∀j,P (s.data j)) raw (fun i => hs i)
  change Execution prog _ _ l (trimIndex cap (tr (Fin.last l))) at out
  rw [he] at out
  exact ⟨l,hl,out⟩

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
