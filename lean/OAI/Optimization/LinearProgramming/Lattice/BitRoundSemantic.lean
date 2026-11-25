import OAI.Optimization.LinearProgramming.Lattice.BitRoundSemanticCore
import OAI.Optimization.LinearProgramming.Lattice.BitRoundingKernels

/-! The verified repeated-direction controller specialized to the actual Gram projection,
closed integral LLL selector and integer Horner arithmetic. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
open OracleSpec

def RequestReached (p M : ℕ) (u : Request) : Prop := RequestReachedWith actualKernels p M u

theorem actual_round_kernel_semantics : RoundKernelSemantics actualKernels where
  selector := actual_selector
  finish := finish_packed
  params := probeParams_packed

theorem stage_directions {p M : ℕ} (hp : 0<p) (hM : 0<M) (v : Fin p→ℝ)
    (o : (Fin p→ℤ)→Bool) (hO : ∀ a, o a = true ↔ 0≤formValue a v)
    (reply : Word→Word) (wire : ∀ a, rowOracle reply (List.ofFn a)=o a)
    (fuel : ℕ) (old : List (Fin p→ℤ)) (valid : DigitInvariant M fuel old) :
    let t := directionsQ M (lllShortSelector M) fuel old
    ∃ steps : List Request, Dialogue actualKernels reply (stage actualKernels (packedEnv M fuel old)) steps
      (signRowWord (radixVector ((2:ℤ)^radixWidth p M) (old.reverse++SignQueries.run o t))) ∧
      steps.map Prod.fst=wordQueries o t ∧ ∀ q∈steps, RequestReached p M q :=
  stage_directions_with actual_round_kernel_semantics hp hM v o hO reply wire fuel old valid

theorem rounding_dialogue {p M : ℕ} (hp : 0<p) (hM : 0<M) (v : Fin p→ℝ)
    (o : (Fin p→ℤ)→Bool) (hO : ∀ a, o a = true ↔ 0≤formValue a v)
    (reply : Word→Word) (wire : ∀ a, rowOracle reply (List.ofFn a)=o a) :
    let t := roundingProgramWith M (lllShortSelector M)
    ∃ steps : List Request, Dialogue actualKernels reply (dispatch actualKernels (.inl (p,M))) steps
      (signRowWord (SignQueries.run o t)) ∧ steps.map Prod.fst = wordQueries o t ∧
      (∀ q∈steps, RequestReached p M q) ∧ steps.length ≤ p*(2*p+1+p*searchPrecision p M) :=
  rounding_dialogue_with actual_round_kernel_semantics hp hM v o hO reply wire

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
