import OAI.Computability.VPVNP.CompressorReaderEnvelope

/-!
# Theorem 8.1 of “VP and VNP differ over every field”

The fixed two-tape table reads the initialized Macaulay and Cramer workspaces
from its polynomial-length advice. At each satisfiable length the same
advised algebra and functional apply to every exponent width. All literal
branches halt by the uniform clock, including the rejecting index guesses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorReader

open Evaluator

/-- Fixed order of the work and advice fields in the evaluator's binary prefix. -/
noncomputable def fields : List (WeightedStep.Port Ports) := Finset.univ.toList

theorem fields_nodup : fields.Nodup := Finset.nodup_toList _
set_option maxRecDepth 5000 in
theorem mem_fields (k : WeightedStep.Port Ports) : k ∈ fields := by
  change k ∈ (Finset.univ : Finset (WeightedStep.Port Ports)).toList
  exact Finset.mem_toList.mpr (Finset.mem_univ k)

/-- The same literal machine table serves every input length and exponent
width, in positive characteristic and in characteristic zero. -/
noncomputable def program : UniversalMachine.Program := MatrixCallbacks.program fields (read true) (read false)

end CompressorReader

namespace Compression.BlockSchedule.Templates

open MvPolynomial LabelEvaluator RAMTape Evaluator.MatrixCallbacks EvaluatorProgramRawInput
open Evaluator.BinaryMachine LiveEvaluatorEncoding

local instance finiteEvaluatorPrime (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- Finite enumeration of the slice ground field for the finite-algebra evaluator. -/
noncomputable local instance finiteEvaluatorGround (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) :=
  Fintype.ofFinite _
/-- Algebra structure on the ambient algebraic closure induced by embedding the slice ground
field. -/
noncomputable local instance finiteEvaluatorAmbient (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

local notation "ports" => Fintype.card (MachinePort (Evaluator.WeightedStep.Port CompressorReader.Ports))

/-- The advised finite reduced algebra and its computation at one length.
The radius bounds all visited head positions and the full encoded tape state. -/
def HasFiniteAlgebraEvaluation (q c power n : ℕ) (hn : 2 ≤ n) : Prop :=
  ∃ p : Nat.Primes, (q ≠ 0 → p.val = q) ∧ (q = 0 → p.val ≤ 2^B.compressorPrimeBits c n) ∧
  ∃ M : Model p (B.compressorDegree n) (B.compressorEquations hn c),
  ∃ adviceBits : List Bool, adviceBits.length ≤ n^power ∧
  Finite M.algebra ∧ IsReduced M.algebra ∧ M.functional 1 = 1 ∧
  (∀ i, eval₂ (Int.castRingHom M.algebra) M.labels (B.compressorEquations hn c i) = 0) ∧
  ∀ Z (es : Fin (B.compressorLabelCount c n) → BurstRAM.Word Z),
    let E := CompressorReader.program
    let raw := adviceBits ++ runtime es
    UniversalMachine.AllHalt E (2^(n^power)*(Z+1)^4) (UniversalMachine.initial E raw) ∧
    (∀ ticks ≥ 2^(n^power)*(Z+1)^4,
      (UniversalMachine.paths E ticks (UniversalMachine.initial E raw) : ZMod p.val) =
        M.functional (∏ i, M.labels i ^ (es i).val)) ∧
    (∀ choices, let disp := choiceDisplacement E (UniversalMachine.initial E raw) choices
      StackCompiler.HeadBox (2240*(ports+1)*(n^power+Z+1)^4) disp.1 disp.2) ∧
    ∀ time (bits : Fin time → Bool) (i : Fin (time+1)),
      StateFits (2240*(ports+1)*(n^power+Z+1)^4)
        (EvaluatorTail.history E time (UniversalMachine.initial E raw) bits i)

/-- The finite reduced algebra, its solution, the advised prime and the fixed
binary evaluator at every sufficiently large satisfiable length. -/
theorem finite_algebra_evaluator (q c : ℕ) [CharP k q] :
    ∃ C N : ℕ, ∀ n ≥ N, ∀ hn : 2 ≤ n,
      (∃ x : Fin (B.compressorLabelCount c n) → k,
        ∀ i, eval₂ (Int.castRingHom k) x (B.compressorEquations hn c i) = 0) →
      B.HasFiniteAlgebraEvaluation q c C n hn := by
  obtain ⟨a,ha,prepare⟩ := B.exists_compressor_reader_envelope CompressorReader.fields q c
  exact B.uniform_evaluator_of_coordinate_readers CompressorReader.fields CompressorReader.fields_nodup
    CompressorReader.mem_fields (CompressorReader.read true) (CompressorReader.read false) q c a ha 0
    (fun n _ ↦ prepare n)

/-- The same fixed evaluator and length exponents at every exceptional small
circuit in the fixed characteristic. The polynomial is computed exactly and
its circuit may contain arbitrary field constants. -/
theorem finite_algebra_evaluator_of_small_circuits (q c : ℕ) [CharP k q] (hc : 1 ≤ c) :
    ∃ power N : ℕ, ∀ n ≥ N, ∀ hn : 2 ≤ n,
      circuitSize (map (Int.castRingHom k) (P n)) ≤ n^c →
      B.HasFiniteAlgebraEvaluation q c power n hn := by
  obtain ⟨power,N,h⟩ := B.finite_algebra_evaluator q c
  refine ⟨power,N,fun n hN hn hs ↦ ?_⟩
  obtain ⟨s,hs,circuit,hpoly⟩ := circuitSize_le_iff.mp hs
  exact h n hN hn (B.exists_compressorSolution_of_circuit hn hc hs circuit hpoly)

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
