import OAI.Optimization.LinearProgramming.Lattice.BitSelectorBridge
import OAI.Optimization.LinearProgramming.Lattice.LLLBitNative
import OAI.Optimization.LinearProgramming.OracleSpec.BitStackDeployment

/-! A single polynomial-time bit program for the native LLL simultaneous-approximation call. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Selector
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

noncomputable def select : Input → ℕ × List ℤ := selectWith lllRows

noncomputable def selectP : Procedure inputCode outputCode select := selectWithP lllRowsP

theorem selectPack {p : ℕ} (M : ℕ) (u : Fin p → ℚ) :
    select (M,List.ofFn u) = ((lllShortSelector M u).1, List.ofFn (lllShortSelector M u).2) :=
  selectWithPack lllRows (fun b hi => lllRows_packMatrix_succ b hi) M u

theorem select_correct {p M : ℕ} (hp : 0 < p) (hM : 0 < M) (u : Fin p → ℚ) :
    0 < (select (M,List.ofFn u)).1 ∧ (select (M,List.ofFn u)).1 ≤ searchDenominator p M ^ (p+1) ∧
      ∀ i : Fin p, |((select (M,List.ofFn u)).1 : ℚ)*u i -
        (readAt 0 (select (M,List.ofFn u)).2 i.val : ℤ)| ≤ 1 / (8 * (p:ℚ)*M) := by
  rw [selectPack]
  simpa only [readAt_ofFn] using lllShortSelector_correct hp hM u

/-- Deployment to finite bit instructions includes serialization and incurs no oracle
history. The one fixed machine works for arbitrary dimension, radii and normalized inputs. -/
theorem selectMachine_correct (o : OracleSpec.WordOracle) {p : ℕ} (M : ℕ) (u : Fin p → ℚ) :
    (OracleSpec.BitCode.deploy selectP).ComputesWithin o (inputCode (M,List.ofFn u))
      (3*selectP.bound.eval (inputCode (M,List.ofFn u)).length+2*(inputCode (M,List.ofFn u)).length+2)
      (fun h w => h=[] ∧ w=outputCode ((lllShortSelector M u).1,List.ofFn (lllShortSelector M u).2)) := by
  simpa only [selectPack] using OracleSpec.BitCode.deploy_correct selectP o (M,List.ofFn u)

end Selector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
