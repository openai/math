import OAI.Computability.NearSquareRoot.FixedCandidateNativeFiles
import OAI.Computability.NearSquareRoot.SelectedKernelProfiles
import OAI.Computability.NearSquareRoot.SynchronizedPermutationPassProgram
import OAI.Computability.NearSquareRoot.FixedLayerPermutationRunDataEffective

/-! # The emitted permutation code on every arithmetic candidate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CandidateParameters
open KernelPass.ComputableSyntax
open IntegerMultiplication Code Filter FixedLayer GeneratorSyntax CommonRegisters
open Benes.PackedBatchHeader EffectiveBoundedTask

/-- The tape program is specified on every tuple. Its clocks and arenas depend
only on the tuple and its current array, including when its reserves are small. -/
structure PermutationMeasurements where
  good : Guess → Prop
  frequent : ∀ j, EventuallyReserves j good
  time : (p : Guess) → NativePass (exterior p) → ℕ
  space : (p : Guess) → NativePass (exterior p) → ℕ
  run : NativeMeasured exterior time space
  sharp : ∀ p, good p → ∀ x,
    time p x = nativeWork (Generator.midExponent (exponent p)) x.val.1 ∧ space p x = x.val.1.volumeB

private def reserves (d : ℕ → ℕ) (p : Guess) : Prop :=
  d (exponent p) ≤ positionLow p ∧ d (exponent p) ≤ positionHigh p ∧
    ⌈Generator.midExponent (exponent p)⌉₊+2 ≤ positionHigh p ∧ d (exponent p) ≤ exterior p

private theorem often (d : ℕ → ℕ) (j : ℕ) : EventuallyReserves j (reserves d) := by
  filter_upwards [eventually_ge_atTop (d j)] with a ha
  filter_upwards [eventually_ge_atTop (max (d j) (⌈Generator.midExponent j⌉₊+2))] with b hb
  filter_upwards [eventually_ge_atTop (d j)] with D hD
  exact ⟨ha,(le_max_left ..).trans hb,(le_max_right ..).trans hb,hD⟩

/-- Instantiate the concrete sparse-mask and position-router source with the
selected midpoint rectangle. The finite register bound is common to every
generated command across all four tuple components. -/
theorem permutationMeasurements (files : NativeFiles) : Nonempty PermutationMeasurements := by
  classical
  obtain ⟨pre,post,mid,compiled⟩ := PassPoint.compile
  let cook := Controlled.Effective.BatchCmd.compile pre post mid
  let cmd p := cook (positionLow p) (positionHigh p) (files.rectangleFile p)
  have law j := compiled (files.rectangle j) (Generator.midExponent j) (by linarith [(midpoint_bounds j).1])
    (midpoint_bounds j).2 (files.contract j)
  choose d fast using fun j => (law j).2
  choose T S slow using fun p => (law (exponent p)).1 (positionLow p) (positionHigh p)
  let price (p : Guess) (x : NativePass (exterior p)) :=
    if reserves d p then nativeWork (Generator.midExponent (exponent p)) x.val.1 else T p x.val
  let cells (p : Guess) (x : NativePass (exterior p)) :=
    if reserves d p then x.val.1.volumeB else S p x.val
  obtain ⟨R,rpos,register⟩ := Controlled.Effective.BatchCmd.within pre post mid files.registers
  refine ⟨⟨reserves d,often d,price,cells,?_,?_⟩⟩
  · refine ⟨cmd,R,Controlled.Effective.BatchCmd.effective pre post mid
      positionLow_pr.to_comp positionHigh_pr.to_comp files.rectangleFile_effective,rpos,fun p =>
      ⟨register _ _ _ (files.within (exponent p)),?_⟩⟩
    by_cases h : reserves d p
    · have doFast := fast (exponent p) (positionLow p) (positionHigh p) h.1 h.2.1 h.2.2.1
        (fun x : NativePass (exterior p) => x.val) (fun x => x.property.symm ▸ h.2.2.2)
      simpa only [price,cells,ite_eq_left h,cmd,cook,NativeFiles.rectangleFile,PassPoint.charge,nativeWork,Function.comp_def] using doFast
    · simpa only [price,cells,ite_eq_right h,cmd,cook,NativeFiles.rectangleFile,Function.comp_def] using (slow p).on (fun x : NativePass (exterior p) => x.val)
  · intro p hp x
    simp [price,cells,hp]

end FixedCandidate.CandidateParameters

end NearSquareRoot
end Computability
end OAI
