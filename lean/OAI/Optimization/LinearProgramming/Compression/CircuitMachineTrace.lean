import OAI.Optimization.LinearProgramming.Compression.CircuitMachine

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace BlockExec

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A block laid out starting at the current program counter is an ordinary RAM trace
in its ambient program. In particular, the code before or after the block is unrestricted. -/
theorem trace_of_layout {code p : Program} {s t : State K} (h : BlockExec code s t)
    (layout : ∀ j : Fin code.length, p[s.pc + j.val]? = some code[j.val]) :
    ∃ v : Fin (code.length+1) → State K, Trace p s code.length v ∧ v (Fin.last _) = t := by
  induction h with
  | nil s =>
    exact ⟨fun _ => s, ⟨rfl, fun i => Fin.elim0 i⟩, rfl⟩
  | @cons i is s u t hlive hi hpc tail ih =>
    have suffixLayout (j : Fin is.length) : p[u.pc + j.val]? = some is[j.val] := by
      have hj := layout j.succ
      rw [hpc]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hj
    obtain ⟨v, ⟨hv0, hvstep⟩, hvlast⟩ := ih suffixLayout
    let w : Fin ((i::is).length+1) → State K := Fin.cons s v
    refine ⟨w, ⟨by simp [w], ?_⟩, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · have hlookup : p[s.pc]? = some i := by simpa using layout 0
        change step p s = some (v 0)
        rw [hv0]
        simpa [step, hlive, hlookup] using hi
      · exact hvstep k
    · exact (Fin.cons_last ..).trans hvlast

/-- A prefix and a suffix may be attached to the compiled code without changing its execution. -/
theorem trace_append {code : Program} {s t : State K} (h : BlockExec code s t)
    (pre suffix : Program) (hpc : s.pc = pre.length) :
    ∃ v : Fin (code.length+1) → State K, Trace (pre ++ code ++ suffix) s code.length v ∧
      v (Fin.last _) = t := by
  apply h.trace_of_layout
  intro j
  rw [List.append_assoc, hpc, List.getElem?_append_right (by omega)]
  simp [List.getElem?_append_left j.isLt, j.isLt]

end BlockExec
end Compression
end LinearProgramming
end Optimization
end OAI
