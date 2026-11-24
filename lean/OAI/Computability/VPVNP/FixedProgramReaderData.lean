import OAI.Computability.VPVNP.FixedProgramModelData
import OAI.Computability.VPVNP.CompressorEvaluatorInput

/-!
# Tail obligations supplied by the literal scalar evaluator

The choice of a monomial basis is part of the length-specific advice.
Re-present the slice model in the order used by the two deterministic
matrix readers. The same raw binary advice then works for every vector
of exponents, with exact monomials on the required range.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression LabelEvaluator RAMTape Evaluator MatrixCallbacks LiveEvaluatorEncoding
open BurstRAM LiveProgram

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩
/-- Enumerate the finite ground field of the selected slice. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- View the ambient field as an algebra over the ground field through the slice embedding. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra

variable {K : Type*} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program) (B : S.Templates)
  {n C : ℕ} (hn : 2 ≤ n) {p : Nat.Primes}
  (M : Model p (B.compressorDegree n) (B.compressorEquations hn C))
  {P : Type} [DecidableEq P] [Fintype P] (ps : List (WeightedStep.Port P))
  (hps : ps.Nodup) (hall : ∀ i, i ∈ ps) (frob label : FiniteRoutine (ReadPort P))

/-- Present the selected slice in the canonical coordinates used by the scalar evaluator. -/
noncomputable abbrev canonicalModel := M.withCanonicalPresentation (B.compressorCanonical hn C M)

/-- Turn the encoded matrix readers and their resource bounds into scalar data for the canonical model. -/
noncomputable def scalarDataOfReader (H : B.SliceReaderAdvice M frob label)
    (hE : D.evaluator = MatrixCallbacks.program ps frob label)
    (hraw : H.envelope ps ≤ n^D.constants.prefixPower)
    (hadvice : (D.geometry n).w+n^D.constants.prefixPower+B.denseCount n C*Nat.clog 2 (B.compressorLabelCount C n)
      ≤ n^D.constants.advicePower)
    (hclock : 2^(6*H.envelope ps+23)*(D.counterWidth n+1)^4 ≤ 2^(D.chainHeight n))
    (hspace : 2240*(Fintype.card (BinaryMachine.MachinePort (WeightedStep.Port P))+1)*(H.envelope ps+D.counterWidth n+1)^4
      ≤ n^D.constants.radiusPower) :
    D.ScalarData B hn (canonicalModel B hn M) := by
  let data := H.binary ps
  have run (xs : Fin (B.compressorLabelCount C n) → ℕ) :=
    H.resources_and_value ps hps hall (D.exponentWords n xs) (2^(D.chainHeight n)) hclock
  refine ⟨data, (H.binary_le ps).trans hraw, hadvice, ?_, ?_, ?_⟩
  · intro xs
    unfold initial
    rw [hE]
    exact (run xs).1
  · intro xs time bs i
    apply LiveEvaluatorRadius.fits_mono hspace
    unfold initial
    rw [hE]
    exact (run xs).2.2.2 time bs i
  · intro xs bound
    rw [(canonicalModel B hn M).branchCount_mod _ xs bound]
    have val (j) : (D.exponentWords n xs j).val = xs j := Nat.mod_eq_of_lt (bound j)
    unfold initial
    rw [hE]
    have hv := (run xs).2.1
    simp only [val] at hv
    exact hv

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
