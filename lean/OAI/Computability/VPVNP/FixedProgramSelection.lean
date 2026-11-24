import OAI.Computability.VPVNP.FixedProgramParameters
import OAI.Computability.VPVNP.FixedProgramReaderData
import OAI.Computability.VPVNP.FiniteAlgebraEvaluator

/-!
# The actual scalar evaluator and the fixed live-program parameters

The matrix readers are fixed controls on a fixed finite port type. Their
per-model resource envelope determines the chain and advice powers. Only
after choosing these powers is the address multiplier increased for the
pair simulation, and only after that are a prime and a finite slice chosen.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program
set_option maxRecDepth 10000

open Compression BurstRAM LiveProgram LabelEvaluator RAMTape CursorNetwork

variable {K : Type*} [Field K] {S : BlockSchedule K} (T : S.Templates)

/-- Number of machine ports in the weighted scalar evaluator with the compressor readers installed. -/
noncomputable def evaluatorPorts :=
  Fintype.card (Evaluator.BinaryMachine.MachinePort (Evaluator.WeightedStep.Port CompressorReader.Ports))

/-- Once the arithmetic bounds are known, every admissible slice has
canonical scalar advice and a literal evaluator satisfying all the tail
obligations on that very slice. -/
theorem selection_of_readers (q C : ℕ) {P : Type} [DecidableEq P] [Fintype P]
    (ps : List (Evaluator.WeightedStep.Port P)) (hps : ps.Nodup) (hall : ∀ j, j ∈ ps)
    (frob label : FiniteRoutine (Evaluator.MatrixCallbacks.ReadPort P)) (E : UniversalMachine.Program)
    (hE : E = Evaluator.MatrixCallbacks.program ps frob label) (qenv : ℕ → ℕ) (henv : PolynomiallyBounded qenv)
    (readers : ∀ n, ∀ (hn : 2 ≤ n) (p : Nat.Primes), (q ≠ 0 → p.val = q) →
      (q = 0 → p.val ≤ 2^T.compressorPrimeBits C n) → ∀ M : Model p (T.compressorDegree n) (T.compressorEquations hn C),
        ∃ H : T.SliceReaderAdvice M frob label, H.envelope ps ≤ qenv n) :
    let u := pairExponents T
    let ports := Fintype.card (Evaluator.BinaryMachine.MachinePort (Evaluator.WeightedStep.Port P))
    ∃ c : Constants, c.circuitExponent = C ∧ c.motifLabels = Fintype.card T.Entry ∧
      2 ≤ c.chainPower ∧ ∃ b₀ : ℕ, 1 ≤ b₀ ∧ ∀ b ≥ b₀, ∀ O : PairTable,
        ∀ᶠ n : ℕ in Filter.atTop, ∃ hb : 1 ≤ b,
          let D := ofPaperConstants c E O b hb (liveRatio u)
          Numerics T D C qenv ports n ∧
            ∀ (hn : 2 ≤ n) (p : Nat.Primes), (q ≠ 0 → p.val = q) → (q = 0 → p.val ≤ 2^T.compressorPrimeBits C n) →
              ∀ M : Model p (T.compressorDegree n) (T.compressorEquations hn C),
                Nonempty (D.ScalarData T hn (canonicalModel T hn M)) := by
  intro u ports
  obtain ⟨c,hC,hm,ha,b₀,hb₀,geometry⟩ := select T C u E qenv henv ports
  refine ⟨c,hC,hm,ha,b₀,hb₀,?_⟩
  intro b hb O
  filter_upwards [geometry b hb O] with n h
  obtain ⟨hpos,G⟩ := h
  let D := ofPaperConstants c E O b hpos (liveRatio u)
  refine ⟨hpos,G,?_⟩
  intro hn p hp hbits M
  obtain ⟨H,hH⟩ := readers n hn p hp hbits M
  have hclock := (Nat.mul_le_mul_right ((D.counterWidth n+1)^4)
    (Nat.pow_le_pow_right (by decide : 0 < 2) (show 6*H.envelope ps+23 ≤ 6*qenv n+23 by omega))).trans G.time
  have hspace := (Nat.mul_le_mul_left (2240*(ports+1))
    (Nat.pow_le_pow_left (show H.envelope ps+D.counterWidth n+1 ≤ qenv n+D.counterWidth n+1 by omega) 4)).trans G.space
  exact ⟨scalarDataOfReader D T hn M ps hps hall frob label H hE (hH.trans G.raw) G.advice hclock hspace⟩

theorem select_scalar (q C : ℕ) :
    let u := pairExponents T
    ∃ (env : ℕ → ℕ) (c : Constants), c.circuitExponent = C ∧ c.motifLabels = Fintype.card T.Entry ∧
      2 ≤ c.chainPower ∧ ∃ b₀ : ℕ, 1 ≤ b₀ ∧ ∀ b ≥ b₀, ∀ O : PairTable,
        ∀ᶠ n : ℕ in Filter.atTop, ∃ hb : 1 ≤ b,
          let D := ofPaperConstants c CompressorReader.program O b hb (liveRatio u)
          Numerics T D C env evaluatorPorts n ∧
            ∀ (hn : 2 ≤ n) (p : Nat.Primes), (q ≠ 0 → p.val = q) → (q = 0 → p.val ≤ 2^T.compressorPrimeBits C n) →
              ∀ M : Model p (T.compressorDegree n) (T.compressorEquations hn C),
                Nonempty (D.ScalarData T hn (canonicalModel T hn M)) := by
  intro u
  obtain ⟨env,henv,readers⟩ := T.exists_compressor_reader_envelope CompressorReader.fields q C
  refine ⟨env,?_⟩
  exact selection_of_readers T q C CompressorReader.fields CompressorReader.fields_nodup
    CompressorReader.mem_fields (CompressorReader.read true) (CompressorReader.read false)
    CompressorReader.program rfl env henv readers

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
