import OAI.Computability.VPVNP.LiveVirtualPairScanCapacity
import OAI.Computability.VPVNP.CompressorCanonicalWorkerInputs

/-! # Selecting all finite ordinal and payload data at an exceptional length -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression CursorNetwork CursorBounds LiveProgram LabelEvaluator Filter
open PairSimulation.LocalHistory ExponentTrace CutSchedule

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant)

/-- One threshold supplies the exact nomination clock, shared payload
capacity and all ordinal worker inputs, before the prime, model, advice
and current pair occurrence are specified. -/
theorem eventually_canonicalScan (C : ℕ) (hb : max S.laneBits 5 ≤ D.addressFactor) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C) [NeZero (virtualBits D.addressFactor n)]
      (p : Nat.Primes) (M : Model p (B.compressorDegree n) (B.compressorEquations hn C))
      (data : D.ScalarData B hn M) (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower))
      (i : D.groupIndices n) (μ : D.pairNom n C), Nonempty (CanonicalScan data V ξ i μ) := by
  filter_upwards [eventually_virtualNominationClock D B u C,eventually_scanWidth D B u C hb,
    CompressorRecords.CanonicalWorker.eventually_execute_inputs.{v,0} B u D.addressFactor hb]
    with n clocks widths inputs hn V inst p M data ξ i μ
  have valid := inputs (laneLabels _ _ V.lanes) V.dimension le_rfl M.algebra
    (B.compressorValues hn M) (B.compressorValues_solution hn M)
  have hbucket : virtualBucket n = 2^roundedUp 1 4 n := by
    simp only [virtualBucket,roundedUp_eq,Nat.cast_one,Nat.cast_ofNat]
  unfold pairInput at valid
  rw [hbucket] at valid
  exact ⟨clocks hn V data.advice ξ i μ, widths hn V p M, valid.some⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
