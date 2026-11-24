import OAI.Computability.VPVNP.FixedNativeProgram
import OAI.Computability.VPVNP.LiveProgramAdviceCapacity
import OAI.Computability.VPVNP.EvaluatorProgramRawInput
import OAI.Computability.VPVNP.RAMTapePhysicalHalting

/-!
# The shared advice and paths of the fixed diagonal program

The program distributes one advice string across the groups. It contains
the raw evaluator advice followed, after padding, by the permutation from
dense physical labels to the joint formal label order. Every midpoint
configuration starts on that very raw advice and the same truncated exponent
words. The weighted pair paths and the native single-group counts must
refer to this common distribution.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression BurstRAM LiveProgram LabelEvaluator CutSchedule ExponentTrace JointLabelSystem
open LiveEvaluatorEncoding UniversalMachine

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩
/-- Enumerate the finite ground field of the selected slice. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- View the ambient field as an algebra over the ground field through the slice embedding. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra


variable {K : Type*} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program) (B : S.Templates)
  {n C : ℕ} (hn : 2 ≤ n) {p : Nat.Primes}
  (M : Model p (B.compressorDegree n) (B.compressorEquations hn C))

/-- Height `h` for which each half of the diagonal chain has `2^h` groups. -/
def chainHeight (n : ℕ) := n^D.constants.chainPower-1
/-- Bit width reserved for each accumulated label exponent. -/
def counterWidth (n : ℕ) := 2*n^D.constants.chainPower

/-- Formal label index at a physical counter position, encoded as an advice word. -/
noncomputable def orderWord (n C : ℕ) (i : Fin (B.denseCount n C)) :
    BurstRAM.Word (Nat.clog 2 (B.compressorLabelCount C n)) :=
  let j := FixedRows.labelOrder B.Entry n C i
  ⟨j.val,j.isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩

/-- Pack the raw evaluator advice and the physical-to-formal label permutation into the shared tape. -/
noncomputable def distributedAdvice (n C : ℕ) (raw : List Bool) : Bits (n^D.constants.advicePower) :=
  Advice.adviceTape (D.geometry n).w (n^D.constants.prefixPower) (n^D.constants.advicePower)
    raw (orderWord B n C)

/-- Encode each exponent modulo the word size used by the evaluator. -/
def exponentWords (n : ℕ) {t : ℕ} (xs : Fin t → ℕ) : Fin t → BurstRAM.Word (D.counterWidth n) :=
  fun j => Fin.ofNat _ (xs j)

/-- Start the evaluator on its raw advice followed by the serialized exponent vector. -/
def initial (n : ℕ) {t : ℕ} (raw : List Bool) (xs : Fin t → ℕ) :=
  UniversalMachine.initial D.evaluator (raw ++ EvaluatorProgramRawInput.runtime (D.exponentWords n xs))

/-- The scalar program at this model has exactly the raw input assembled
by the midpoint stages. The range statement covers all branch histories,
so it also covers the initial configuration in the absence of an accepting path. -/
structure ScalarData where
  /-- Raw binary reader advice for this finite model. -/
  raw : List Bool
  rawLength : raw.length ≤ n^D.constants.prefixPower
  adviceSpace : (D.geometry n).w+n^D.constants.prefixPower+B.denseCount n C*Nat.clog 2 (B.compressorLabelCount C n)
    ≤ n^D.constants.advicePower
  halt : ∀ xs : Fin (B.compressorLabelCount C n) → ℕ,
    AllHalt D.evaluator (2^(D.chainHeight n)) (D.initial n raw xs)
  space : ∀ (xs : Fin (B.compressorLabelCount C n) → ℕ) (time : ℕ) (bs : Fin time → Bool) (i : Fin (time+1)),
    StateFits (n^D.constants.radiusPower) (EvaluatorTail.history D.evaluator time (D.initial n raw xs) bs i)
  value : ∀ xs : Fin (B.compressorLabelCount C n) → ℕ, (∀ i, xs i < 2^(D.counterWidth n)) →
    (paths D.evaluator (2^(D.chainHeight n)) (D.initial n raw xs) : ZMod p.val) =
      (M.presentation.branchCount p.val (D.counterWidth n) xs : ZMod p.val)

variable {D B hn M} (data : D.ScalarData B hn M)

/-- Shared chain advice obtained by packing the scalar reader advice and label order. -/
noncomputable def ScalarData.advice := D.distributedAdvice B n C data.raw

/-- Encode the midpoint evaluator configuration after reindexing the physical counters. -/
noncomputable def ScalarData.init (xs : Fin (B.denseCount n C) → ℕ) :=
  LiveEvaluatorTail.initialCode (n^D.constants.radiusPower)
    (D.initial n data.raw (B.formalExponents xs))

theorem ScalarData.init_state (xs : Fin (B.denseCount n C) → ℕ) :
    (data.init xs).toState = EvaluatorTail.canonical (D.initial n data.raw (B.formalExponents xs)) :=
  LiveEvaluatorTail.initialCode_toState _ (data.space (B.formalExponents xs) 0 Fin.elim0 0)

theorem ScalarData.histories (xs : Fin (B.compressorLabelCount C n) → ℕ) :
    LiveEvaluatorTail.HistoriesFit D.evaluator (n^D.constants.radiusPower) (2^(D.chainHeight n))
      (D.initial n data.raw xs) :=
  fun bs _ i => data.space xs _ bs i

variable (fit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)

set_option maxHeartbeats 800000 in
/-- Finite weighted paths for each pair whose sum recovers its nominated grammar multiplicity. -/
structure PairData where
  /-- Path choices for this exterior, pair index and production nomination. -/
  Path : Exterior (D.chainHeight n) (n^D.constants.deltaPower) → Fin (2^(D.chainHeight n)) →
    Compression.BlockSchedule.Templates.PairNomination n C (D.geometry n).d → Type
  [pathFintype : ∀ ξ i μ, Fintype (Path ξ i μ)]
  /-- Compressor label exponents contributed by one pair path. -/
  ν : ∀ ξ i μ, Path ξ i μ → B.Entry → ℕ
  bounded : ∀ ξ i μ q v, ν ξ i μ q v < 2^(2*(D.geometry n).d)
  weight : ∀ ξ i μ, (∑ q : Path ξ i μ, ∏ v, (B.compressorValues hn M v)^ν ξ i μ q v) =
    (GrammarDiagonal.multiplicity (⟨n-1,by omega⟩ : Fin n) (⟨0,pow_pos (by omega) _⟩ : Fin (n^(C+5)))
      (PairedChain.siteInput (h := D.chainHeight n) (Δ := n^D.constants.deltaPower) (n := n)
        (r := (D.geometry n).d) (bucket := (D.geometry n).H) (w := (D.geometry n).w) D.literal fit data.advice ξ i) μ : M.algebra)

attribute [instance] PairData.pathFintype

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
