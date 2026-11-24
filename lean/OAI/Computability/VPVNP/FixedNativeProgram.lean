import OAI.Computability.VPVNP.FixedModelDiagonal
import OAI.Computability.VPVNP.LiveProgram
import OAI.Computability.VPVNP.LiveTranscriptCoefficients

/-!
# Choosing the exceptional length after the literal program

The same pair table, evaluator, public operand formulas, and layout powers
serve every candidate length. The actual compiled coefficient machine then
has one common eventual threshold. At a candidate small-circuit length the
integer equations supply the prime and a finite algebra. Only at that point
are the advice, weighted paths and evaluator configurations selected.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal


open Compression BurstRAM LiveProgram RAMTape LabelEvaluator Filter MvPolynomial

/-- The finite tables and exponents chosen before the exceptional length. -/
structure Program where
  /-- Powers and label counts used by the live program at every input length. -/
  constants : Constants
  /-- Scalar evaluator installed in the second half of the diagonal chain. -/
  evaluator : UniversalMachine.Program
  /-- Finite instruction table for a pair in the first half of the chain. -/
  pair : PairTable
  /-- Multiplier of the binary address width at input length n. -/
  addressFactor : ℕ
  address_pos : 1 ≤ addressFactor
  /-- Numerator of the rational exponent used to compute the live bucket size. -/
  numerator : ℕ
  /-- Denominator of the rational exponent used to compute the live bucket size. -/
  denominator : ℕ
  bucket_lt : numerator < denominator
  /-- Initial persistent word supplied to the live RAM program. -/
  initialLiteral : ℕ

namespace Program

variable (D : Program)

theorem denominator_pos : 0 < D.denominator := Nat.zero_lt_of_lt D.bucket_lt

/-- The linked RAM instruction table with the chosen evaluator and pair code. -/
abbrev native := LiveProgram.program D.constants D.evaluator D.pair
/-- Public operand expressions passed to the linked RAM table. -/
abbrev operands := LiveProgram.operand D.constants D.evaluator D.pair

/-- The fixed universal-machine program obtained by compiling the live RAM table and its operand expressions. -/
@[irreducible] noncomputable def literal : UniversalMachine.Program := SiteProcessorPorts.machine D.native D.operands
  D.addressFactor D.numerator D.denominator 10000 D.initialLiteral D.denominator_pos

theorem literal_eq : D.literal = SiteProcessorPorts.machine D.native D.operands
    D.addressFactor D.numerator D.denominator 10000 D.initialLiteral D.denominator_pos := by unfold literal; rfl

/-- Address width, bucket size and word width of the live program at the given input length. -/
def geometry (n : ℕ) : Geometry :=
  ⟨n, addressWidth D.addressFactor n, 2^(roundedUp D.numerator D.denominator n), CursorBounds.wordBits D.addressFactor n⟩

/-- Instantiate the linked RAM table with public words computed from the compiled program prefix. -/
noncomputable def liveMachine (n : ℕ) :=
  D.native.instantiate (D.geometry n).w (fun i => Pieces.word (D.geometry n) (CounterPublic.actualPrefix D.literal) (D.operands i))

/-- Every public operand expression fits the available word width at this length. -/
def OperandFits (n : ℕ) : Prop :=
  ∀ j, (InputOperandStartup.Expr D.operands j).Fits (D.geometry n) (2^(D.geometry n).w)

variable {K : Type*} [Field K] {S : BlockSchedule K} (B : S.Templates)

/-- Local realization for one chosen joint model. Its fields consist of
individual pair weights, individual tail counts and native one-group path
counts. The actual shared processor coefficient is proved separately. -/
noncomputable abbrev Certificate {n C : ℕ} (hn : 2 ≤ n) {p : Nat.Primes}
    (M : Model p (B.compressorDegree n) (B.compressorEquations hn C))
    (fit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w) :=
  B.LocalCertificate hn M (n^D.constants.chainPower-1) (n^D.constants.deltaPower) (n^D.constants.advicePower)
    (D.geometry n).d (roundedUp D.numerator D.denominator n) (D.geometry n).w (2*n^D.constants.chainPower)
    (n^D.constants.radiusPower) D.literal fit D.evaluator (D.liveMachine n) (n^10000)
    (Fin.ofNat (2^(D.geometry n).w) D.initialLiteral)

/-- At sufficiently large lengths the fixed tables meet the local model
obligations for the primes furnished by the arithmetic specialization. -/
def Realizes (q C : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, D.OperandFits n ∧
    ∀ (hn : 2 ≤ n) (p : Nat.Primes),
      (q ≠ 0 → p.val = q) → (q = 0 → p.val ≤ 2^B.compressorPrimeBits C n) →
      Nonempty (Model p (B.compressorDegree n) (B.compressorEquations hn C)) →
      ∀ fit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w,
        ∃ M : Model p (B.compressorDegree n) (B.compressorEquations hn C), Nonempty (D.Certificate B hn M fit)

end Program

end FixedProgramDiagonal

end VPVNP
end Computability
end OAI
