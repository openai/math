import OAI.Optimization.LinearProgramming.RAM.Code
import OAI.Optimization.LinearProgramming.RAM.RAMCount
import OAI.Optimization.LinearProgramming.Specification

/-! Placing a decoder at an arbitrary return address and serializing the halt tag. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Block RAM.Tape

/-- Decoder correctness only observes the final scalar bank and the designated halt tag. -/
theorem optimizationOutput_congr {m d : Nat} {A : Matrix (Fin m) (Fin d) ℚ}
    {b : Fin m → ℚ} {c : Fin d → ℚ} {s t : State ℚ} (ht : s.output = t.output)
    (hd : s.data = t.data) : OptimizationOutput A b c s ↔ OptimizationOutput A b c t := by
  have hv (a n : Nat) : readVector s a n = readVector t a n := by
    funext i; exact congrFun hd (a+i.val)
  simp only [OptimizationOutput,ht,hd,hv]

/-- Link one of the three checked decoders to its specified halt tag inside a larger
program. Every intermediate state satisfies the same scalar-register bound. -/
theorem decoder_exit {m d k pc tag H : Nat} {A : Matrix (Fin m) (Fin d) ℚ}
    {b : Fin m → ℚ} {c : Fin d → ℚ} {decoder : Block} {p : Program} {s t : Memory ℚ}
    (run : Eval (Good (fun q => ratBits q ≤ H)) decoder s k t)
    (code : CodeAt p pc (decoder.compile pc ++ [.halt tag]))
    (hout : OptimizationOutput A b c {t.atPC 0 with output := some tag}) :
    ∃ z, Execution p (scalarBound H) (s.atPC pc) (k+1) z ∧ OptimizationOutput A b c z := by
  have work := run.compile_correct code.left
  have hstop := code.right.head
  rw [length_compile] at hstop
  let z := {t.atPC (pc+decoder.size) with output := some tag}
  have halt : Execution p (scalarBound H) (t.atPC (pc+decoder.size)) 1 z :=
    .one run.safe_end (by simp [step,Memory.atPC,hstop,execInstr,z]) run.safe_end
  exact ⟨z,work.append halt,(optimizationOutput_congr (s := z) rfl rfl).2 hout⟩

end PrimalDual
end LinearProgramming
end Optimization
end OAI
