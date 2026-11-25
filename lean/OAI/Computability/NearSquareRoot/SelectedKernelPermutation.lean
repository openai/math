import OAI.Computability.NearSquareRoot.FixedCandidatePermutationMeasurements
import OAI.Computability.NearSquareRoot.FixedLayerPermutationRunProfile

/-! # The generated Fourier permutation procedure on the common arithmetic tuple -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CandidateParameters
open KernelPass.ComputableSyntax

open IntegerMultiplication Filter FixedLayer DigitPacking SynchronizedPermutationBudget

/-- For each direction the emitted Fourier permutation command runs on every accepted
tuple. Sufficient low, high and exterior reserves give linear space and the midpoint
row clock. The threshold and the choice of resource estimates are proof data only. -/
theorem permutationProcedure (files : NativeFiles) (degree : ℕ) (dir : Bool) :
    Nonempty (Procedure degree (.permutation dir)) := by
  obtain ⟨m⟩ := permutationMeasurements files
  let η p := Generator.midExponent (exponent p)
  let n := operandWidth degree
  have hn p (x : Input degree p) : 2 ≤ n p x := (inputCut_ge_two degree p).trans x.property
  have big p (x : Input degree p) : BoxPasses (addressBits (n p x)) (exterior p) 2 :=
    (accepted_width x.property).2.2
  have pos p (_ : m.good p) : 0 ≤ η p := by dsimp [η]; linarith [(midpoint_bounds (exponent p)).1]
  obtain ⟨arena,clock,run,_,efficient⟩ := effectivePermutationNativeProfile n (directory degree)
    (fun _ _ => dir) exterior exterior_pr.to_comp (axes degree) hn big η m.good
    pos m.time m.space m.run (fun p h => ⟨1,1,0,fun u _ => by
      obtain ⟨time,space⟩ := m.sharp p h u
      rw [time,space]
      simp only [Nat.one_mul]
      exact ⟨Nat.le_succ _,Nat.le_succ _⟩⟩)
  refine ⟨⟨arena,clock,run,fun j => ?_⟩⟩
  filter_upwards [m.frequent j] with a ha
  filter_upwards [ha] with b hb
  filter_upwards [hb] with D ready
  obtain ⟨area,rate⟩ := efficient (j,a,b,D) ready
  exact ⟨⟨1,area.mono (fun N eq => by rw [eq,Nat.one_mul]; omega)⟩,rate⟩

end FixedCandidate.CandidateParameters

end NearSquareRoot
end Computability
end OAI
