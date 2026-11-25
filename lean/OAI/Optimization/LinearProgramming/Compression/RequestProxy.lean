import OAI.Optimization.LinearProgramming.Compression.RequestFamily
import OAI.Optimization.LinearProgramming.Compression.CommitOracle

/-! Building request rows using the sign computations on the finite list of magnitudes.
Only a reduced basis of the finite rational graph matrix is required from LLL. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- The proxy of one positive scalar magnitude, shared by all requests using it. -/
noncomputable def requestMagnitudeProxy (fuel k : ℕ) (m : ℚ) : ℝ :=
  logProxyValue k m (logProxyNumerator fuel k m)

/-- Strict-negative affine comparison on the currently listed minor magnitudes. -/
def requestMagnitudeNegative {d : ℕ} (fuel k : ℕ) (mag : Fin d → ℚ) (z : Fin d → ℤ) (c : ℤ) : Bool :=
  decide (logProxySign fuel k c z mag = .lt)

theorem requestMagnitudeNegative_correct {d : ℕ} (fuel k : ℕ) (mag : Fin d → ℚ)
    (hm : ∀ i, 0 < mag i) (z : Fin d → ℤ) (c : ℤ) :
    requestMagnitudeNegative fuel k mag z c = true ↔
      requestForm (fun i => requestMagnitudeProxy fuel k (mag i)) z + c < 0 := by
  rw [requestMagnitudeNegative, decide_eq_true_eq, logProxySign_correct fuel k c z mag hm]
  let v := requestForm (fun i => requestMagnitudeProxy fuel k (mag i)) z
  change (if c + v < 0 then Ordering.lt else if 0 < c + v then .gt else .eq) = .lt ↔ v + c < 0
  rw [add_comm v]
  split_ifs <;> simp_all

/-- Rounding for a single request, at the comparison cutoff used by the graph test. -/
def roundedRequestVector {d : ℕ} (fuel k : ℕ) (mag : Fin d → ℚ) : Fin d → ℚ :=
  generatorCommit fuel k ((d+2)*(requestCutoff d+3)) mag

theorem roundedRequestVector_signs {d : ℕ} (fuel k : ℕ) (mag : Fin d → ℚ)
    (hm : ∀ i, 0 < mag i) :
    RequestSigns (fun i => requestMagnitudeProxy fuel k (mag i))
      (fun i => roundedRequestVector fuel k mag i) ((d+2)*(requestCutoff d+3)) := by
  exact (generatorCommit_correct fuel k _ (by positivity) mag hm).2.2.2.2

/-- A function computing reduced rational rows of the stated graph matrix. -/
abbrev GraphRowReducer :=
  ∀ n : ℕ, (Fin (n+1) → ℚ) → Fin (n+1) → Fin ((n+1)+1) → ℚ

/-- The actual postconditions from ordinary rational LLL applied to graph input rows. -/
structure CorrectGraphRowReducer (reduce : GraphRowReducer) : Prop where
  spec : ∀ n (w : Fin (n+1) → ℚ),
    LinearIndependent ℝ (fun i => requestRealRow (reduce n w i)) ∧
    OAI.Optimization.LinearProgramming.Lattice.LLLReduced (fun i => requestRealRow (reduce n w i)) ∧
    Submodule.span ℤ (Set.range (reduce n w)) = Submodule.span ℤ (Set.range (requestInputRows w))

variable {ι : Type*} [LinearOrder ι]

/-- Complete per-request numerical data path from the listed positive rational magnitudes:
rounding, graph reduction, deterministic basis scan, and grid bisection. -/
def latticeRequestRaw (reduce : GraphRowReducer) (fuel k q : ℕ) (mag : ι → ℚ)
    (J : Finset ι) (u : ι) : Option ((Fin J.card → ℚ) × ℚ) :=
  let m := fun i => mag (requestIndices J u i)
  let w := roundedRequestVector fuel k m
  let rows := reduce J.card w
  runMinorRequest w (fun i => requestDecodeRow (rows i)) (requestMagnitudeNegative fuel k m) q

theorem latticeRequestRaw_family (reduce : GraphRowReducer) (hreduce : CorrectGraphRowReducer reduce)
    (fuel k q : ℕ) (hq : 0 < q) (mag : ι → ℚ) (hm : ∀ i, 0 < mag i)
    (U J : Finset ι) (hJ : IsDissociated (fun i => requestMagnitudeProxy fuel k (mag i)) J) :
    let l := fun i => requestMagnitudeProxy fuel k (mag i)
    let raw := latticeRequestRaw reduce fuel k q mag J
    let F := knownRequestFamily U J raw
    let H := requestCutoff (J.card+1)*q
    ∀ u ∈ acceptedRequests U J raw,
      |F.eval (fun j : J => l j) u - l u| ≤ 1 / (q : ℝ) ∧
      (∀ j, (F.coefficient u j).num.natAbs ≤ H ∧ (F.coefficient u j).den ≤ H) ∧
      (F.offset u).num.natAbs ≤ H ∧ (F.offset u).den ≤ H := by
  let m := fun u i => mag (requestIndices J u i)
  let w := fun u => roundedRequestVector fuel k (m u)
  exact knownRequestFamily_spec _ U J hJ q hq w (fun u => reduce J.card (w u))
    (fun u => requestMagnitudeNegative fuel k (m u))
    (fun u => requestMagnitudeNegative_correct _ _ _ fun i => hm (requestIndices J u i))
    (fun u => roundedRequestVector_signs _ _ _ fun i => hm (requestIndices J u i))
    (fun u => hreduce.spec _ (w u))

theorem latticeRequestRaw_restartTest (reduce : GraphRowReducer) (hreduce : CorrectGraphRowReducer reduce)
    (fuel k q : ℕ) (hq : 0 < q) (mag : ι → ℚ) (hm : ∀ i, 0 < mag i)
    (commit : ∀ J : Finset ι, J → ℚ) :
    RestartTest (fun i => requestMagnitudeProxy fuel k (mag i))
      (evaluateMinorRequest commit (latticeRequestRaw reduce fuel k q mag)) := by
  let m := fun (J : Finset ι) u i => mag (requestIndices J u i)
  let w := fun (J : Finset ι) u => roundedRequestVector fuel k (m J u)
  exact evaluated_request_restartTest _ commit q hq w (fun J u => reduce J.card (w J u))
    (fun J u => requestMagnitudeNegative fuel k (m J u))
    (fun J u => requestMagnitudeNegative_correct _ _ _ fun i => hm (requestIndices J u i))
    (fun J u => roundedRequestVector_signs _ _ _ fun i => hm (requestIndices J u i))
    (fun J u => hreduce.spec _ (w J u))

end Compression
end LinearProgramming
end Optimization
end OAI
