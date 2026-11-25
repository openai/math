import OAI.Optimization.LinearProgramming.Compression.PowerPairPackingRun
import OAI.Optimization.LinearProgramming.RAM.CallableRawTapes
import OAI.Optimization.LinearProgramming.Compression.ProxyPrepared
import OAI.Optimization.LinearProgramming.Compression.BlockFootprint

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

/-- The raw-power staging proof discharges every field of the physical
odd-caller to even-callee tape copier's callable input specification. -/
theorem PowerPairsReady.rawTapes {K : Type*} [Field K] {xs : List K} {es : List ℤ}
    {sb ab : ℕ} {initial final : Memory K} (h : PowerPairsReady xs es sb ab initial final) :
    Callable.RawTapes final sb ab (initial.index 60) (powerPairScalarWords xs)
      (powerEncoderAddressInput (signedBitTape es)) :=
  ⟨h.scalarPointer,h.scalarLength,h.addressPointer,h.addressLength,h.oldExtent,h.scalar,h.address⟩

theorem packPowerPairsBlock_footprint {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K → Prop} {word : Block} {initial final : Memory K} {k B : ℕ}
    (run : Block.Eval (Memory.AllData P) (packPowerPairsBlock word) initial k final)
    (foot : Footprint B (initial.atPC 0)) :
    Footprint (max B (addressBudget ((packPowerPairsBlock word).compile 0))+k) (final.atPC 0) :=
  powerPackingStage_footprint run foot

/-- Match the compacted symbolic branch, including its leading cleared constant,
to the paper's numerical proxy query representation. -/
theorem symbolicProxyPairTapes {n : ℕ} (fuel prec : ℕ) (c : ℤ) (a : Fin n → ℤ)
    (mag : Fin n → ℚ) (hs : proxyLargeIndices fuel prec mag ≠ []) {sb ab : ℕ}
    {initial final : Memory ℚ} :
    let D := (2 : ℕ)^(prec+2)
    let grid := fun i => (logProxyNumerator fuel prec (mag i)).getD 0
    let is := proxyLargeIndices fuel prec mag
    let pairs := proxyPowerOperands is (clearedProxyOffset is.toFinset D c a grid) D a mag
    PowerPairsReady (pairs.map Prod.fst) (pairs.map Prod.snd) sb ab initial final →
      Callable.RawTapes final sb ab (initial.index 60) (preparedProxyQuery fuel prec c a mag).scalar
        (preparedProxyQuery fuel prec c a mag).address := by
  dsimp only
  intro h
  simpa only [preparedProxyQuery, ite_eq_right hs, powerPairScalarWords, powerTapeScalarInput]
    using h.rawTapes

end Compression
end LinearProgramming
end Optimization
end OAI
