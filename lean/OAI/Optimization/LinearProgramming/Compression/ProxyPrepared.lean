import OAI.Optimization.LinearProgramming.Compression.SmallProxy
import OAI.Optimization.LinearProgramming.Compression.ProxyPowerOperands
import OAI.Optimization.LinearProgramming.Compression.PowerTapeEncoder
import OAI.Optimization.LinearProgramming.Compression.PowerTapeRAM
import Mathlib.Data.List.FinRange

/-! Deterministic prepared input for the one fixed sign-comparison program.
Only the explicitly named terms of the affine query are enumerated. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- Traverse the concrete list of term numbers, in their ordinary numerical order. -/
def proxyLargeIndices {n : ℕ} (fuel prec : ℕ) (mag : Fin n → ℚ) : List (Fin n) :=
  (List.finRange n).filter fun i => (logProxyNumerator fuel prec (mag i)).isNone

theorem mem_proxyLargeIndices {n : ℕ} (fuel prec : ℕ) (mag : Fin n → ℚ) (i : Fin n) :
    i ∈ proxyLargeIndices fuel prec mag ↔ logProxyNumerator fuel prec (mag i) = none := by
  simp [proxyLargeIndices]

theorem proxyLargeIndices_perm {n : ℕ} (fuel prec : ℕ) (mag : Fin n → ℚ) :
    (proxyLargeIndices fuel prec mag).Perm
      (Finset.univ.filter fun i => logProxyNumerator fuel prec (mag i) = none).toList := by
  apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange n).filter _) (Finset.nodup_toList _)).2
  intro i
  simp

theorem proxyLargeIndices_empty_iff {n : ℕ} (fuel prec : ℕ) (mag : Fin n → ℚ) :
    proxyLargeIndices fuel prec mag = [] ↔ ∀ i, logProxyNumerator fuel prec (mag i) ≠ none := by
  constructor
  · intro h i hi
    have ht := (mem_proxyLargeIndices fuel prec mag i).2 hi
    simp [h] at ht
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    exact h i ((mem_proxyLargeIndices fuel prec mag i).mp hi)

structure ProxyQueryTapes where
  symbolic : Bool
  address : List ℕ
  scalar : List ℚ

/-- Prepare the branch-specific numerical operands after gridding the minor magnitudes.
The all-small tape contains the separate inputs to the dot product. The symbolic
tape contains literal signed exponent bits, and the scalar bases stay separate. -/
def preparedProxyQuery {n : ℕ} (fuel prec : ℕ) (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ) :
    ProxyQueryTapes :=
  let D := (2 : ℕ)^(prec+2)
  let grid i := (logProxyNumerator fuel prec (mag i)).getD 0
  let indices := proxyLargeIndices fuel prec mag
  if indices = [] then
    ⟨false, [n+1], 0 :: 0 :: 0 :: affineInputPairs (smallProxyLeft D a) (smallProxyRight c grid)⟩
  else
    let offset := clearedProxyOffset indices.toFinset D c a grid
    let ps := proxyPowerOperands indices offset D a mag
    ⟨true, powerEncoderAddressInput (signedBitTape (ps.map Prod.snd)), powerTapeScalarInput (ps.map Prod.fst)⟩

end Compression
end LinearProgramming
end Optimization
end OAI
