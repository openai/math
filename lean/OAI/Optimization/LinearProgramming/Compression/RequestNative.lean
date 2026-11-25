import OAI.Optimization.LinearProgramming.Compression.RequestRows
import OAI.Optimization.LinearProgramming.Compression.CommitProgram
import OAI.Optimization.LinearProgramming.Lattice.ShortSelector

/-! Two applications of the verified rational LLL implementation: one for the bounded
rounding of the requested proxies and one for the basis of their rational graph. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- LLL reduction of the graph of the rounded minor logarithms. -/
def nativeGraphRowReducer : GraphRowReducer := fun _ w => Lattice.reduceRational (requestInputRows w)

theorem nativeGraphRowReducer_correct : CorrectGraphRowReducer nativeGraphRowReducer := by
  constructor
  intro n w
  have hi : LinearIndependent ℝ (fun i => Lattice.euclideanRow (requestInputRows w i)) :=
    requestRealRow_input_independent w
  obtain ⟨hr, he⟩ := Lattice.reduceRational_spec (requestInputRows w) hi
  exact ⟨Lattice.independent_of_same_integer_row_lattice hi he, hr, he⟩

/-- A rational vector that preserves all affine comparisons in the §3.2 cutoff, obtained
by running the sign-query rounding program with the LLL simultaneous-approximation selector. -/
def nativeRequestRounded {d : ℕ} (fuel k : ℕ) (mag : Fin d → ℚ) : Fin d → ℚ :=
  let M := (d+2)*(requestCutoff d+3)
  computeCommitWith M (Lattice.lllShortSelector M) (requestMagnitudeNegative fuel k mag)

theorem nativeRequestRounded_correct {d : ℕ} (fuel k : ℕ) (mag : Fin d → ℚ)
    (hm : ∀ i, 0 < mag i) :
    let M := (d+2)*(requestCutoff d+3)
    let w := nativeRequestRounded fuel k mag
    (∀ i, (w i).num.natAbs.size ≤ affineCommitWidth d M ∧ (w i).den.size ≤ affineCommitWidth d M) ∧
    RequestSigns (fun i => requestMagnitudeProxy fuel k (mag i)) (fun i => w i) M := by
  let M := (d+2)*(requestCutoff d+3)
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨height, _, signed⟩ := computeCommitWith_spec (fun i => requestMagnitudeProxy fuel k (mag i)) hM
    (Lattice.lllShortSelector M) (Lattice.lllShortSelector_correct (Nat.succ_pos d) hM)
    (requestMagnitudeNegative fuel k mag) (requestMagnitudeNegative_correct fuel k mag hm)
  exact ⟨height, signed⟩

variable {ι : Type*} [LinearOrder ι]

/-- Request routine using rational LLL from the supplied magnitudes through to rational
affine coefficients. Both applications of lattice reduction are part of the computation. -/
def nativeMinorRequest (fuel k q : ℕ) (mag : ι → ℚ) (J : Finset ι) (u : ι) :
    Option ((Fin J.card → ℚ) × ℚ) :=
  let m := fun i => mag (requestIndices J u i)
  let w := nativeRequestRounded fuel k m
  let r := nativeGraphRowReducer J.card w
  runMinorRequest w (fun i => requestDecodeRow (r i)) (requestMagnitudeNegative fuel k m) q

theorem nativeMinorRequest_restartTest (fuel k q : ℕ) (hq : 0 < q) (mag : ι → ℚ)
    (hm : ∀ i, 0 < mag i) (commit : ∀ J : Finset ι, J → ℚ) :
    RestartTest (fun i => requestMagnitudeProxy fuel k (mag i))
      (evaluateMinorRequest commit (nativeMinorRequest fuel k q mag)) := by
  let m := fun (J : Finset ι) u i => mag (requestIndices J u i)
  let w := fun (J : Finset ι) u => nativeRequestRounded fuel k (m J u)
  exact evaluated_request_restartTest _ commit q hq w (fun J u => nativeGraphRowReducer J.card (w J u))
    (fun J u => requestMagnitudeNegative fuel k (m J u))
    (fun J u => requestMagnitudeNegative_correct _ _ _ fun i => hm (requestIndices J u i))
    (fun J u => (nativeRequestRounded_correct _ _ _ fun i => hm (requestIndices J u i)).2)
    (fun J u => nativeGraphRowReducer_correct.spec _ (w J u))

theorem nativeMinorRequest_goodRequestRows [Fintype ι] (N fuel k : ℕ) (mag : ι → ℚ)
    (hm : ∀ i, 0 < mag i) : GoodRequestRows N (fun i => requestMagnitudeProxy fuel k (mag i))
      (nativeMinorRequest fuel k (paperGrid N) mag) := by
  constructor
  intro J hJ
  let m := fun u i => mag (requestIndices J u i)
  let w := fun u => nativeRequestRounded fuel k (m u)
  exact knownRequestFamily_spec _ Finset.univ J hJ (paperGrid N) (by unfold paperGrid; positivity) w
    (fun u => nativeGraphRowReducer J.card (w u)) (fun u => requestMagnitudeNegative fuel k (m u))
    (fun u => requestMagnitudeNegative_correct _ _ _ fun i => hm (requestIndices J u i))
    (fun u => (nativeRequestRounded_correct _ _ _ fun i => hm (requestIndices J u i)).2)
    (fun u => nativeGraphRowReducer_correct.spec _ (w u))

end Compression
end LinearProgramming
end Optimization
end OAI
