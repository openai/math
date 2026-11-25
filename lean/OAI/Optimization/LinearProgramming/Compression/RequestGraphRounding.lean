import OAI.Optimization.LinearProgramming.Compression.RequestNativeRAM

/-! Bounded rational rounding from a strict affine comparison oracle for an
arbitrary real vector. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open _root_.OAI.Optimization.LinearProgramming.Lattice

/-- The same sign-only rational rounding applies to a real vector through
any strict affine-negative comparison procedure. -/
abbrev roundedFor {d : ℕ} (neg : (Fin d → ℤ) → ℤ → Bool) : Fin d → ℚ :=
  let M := (d+2)*(requestCutoff d+3)
  computeCommitWith M (lllShortSelector M) neg

theorem roundedFor_spec {d : ℕ} (v : Fin d → ℝ) (neg : (Fin d → ℤ) → ℤ → Bool)
    (hneg : ∀ a c, neg a c=true ↔ requestForm v a+c<0) :
    let M := (d+2)*(requestCutoff d+3)
    let w := roundedFor neg
    (∀ i, (w i).num.natAbs.size ≤ RequestScreen.requestRoundBitsFormula d ∧
      (w i).den.size ≤ RequestScreen.requestRoundBitsFormula d) ∧
    RequestSigns v (fun i => w i) M := by
  intro M w
  have hM : 0<M := by dsimp [M]; positivity
  obtain ⟨height,_,hs⟩ := computeCommitWith_spec v hM (lllShortSelector M)
    (lllShortSelector_correct (Nat.succ_pos d) hM) neg hneg
  refine ⟨?_,hs⟩
  intro i
  have cap := RequestScreen.requestRoundBits_width d
  exact ⟨(height i).1.trans cap,(height i).2.trans cap⟩

variable {ι : Type*}

/-- The ordered generators are followed by the newly requested coordinate. The
strict affine sign oracle is the only numerical input to either reduction. -/
def requestUsingSigns (q : ℕ)
    (neg : ∀ J : Finset ι, ι → (Fin (J.card+1) → ℤ) → ℤ → Bool)
    (J : Finset ι) (u : ι) : Option ((Fin J.card → ℚ) × ℚ) :=
  let w := roundedFor (neg J u)
  runMinorRequest w (fun i => requestDecodeRow (nativeGraphRowReducer J.card w i)) (neg J u) q

theorem requestUsingSigns_magnitude [LinearOrder ι] (fuel k q : ℕ) (mag : ι → ℚ) :
    requestUsingSigns q (fun J u => requestMagnitudeNegative fuel k (fun i => mag (requestIndices J u i))) =
      nativeMinorRequest fuel k q mag := rfl

theorem requestUsingSigns_restartTest [LinearOrder ι] (v : ι → ℝ)
    (neg : ∀ J : Finset ι, ι → (Fin (J.card+1) → ℤ) → ℤ → Bool)
    (hneg : ∀ J u a c, neg J u a c=true ↔ requestForm (fun i => v (requestIndices J u i)) a+c<0)
    (q : ℕ) (hq : 0<q) (commit : ∀ J : Finset ι, J → ℚ) :
    RestartTest v (evaluateMinorRequest commit (requestUsingSigns q neg)) := by
  let w := fun (J : Finset ι) u => roundedFor (neg J u)
  exact evaluated_request_restartTest v commit q hq w (fun J u => nativeGraphRowReducer J.card (w J u))
    neg hneg (fun J u => (roundedFor_spec _ (neg J u) (hneg J u)).2)
    (fun J u => nativeGraphRowReducer_correct.spec J.card (w J u))

theorem requestUsingSigns_goodRequestRows [LinearOrder ι] [Fintype ι] (N : ℕ) (v : ι → ℝ)
    (neg : ∀ J : Finset ι, ι → (Fin (J.card+1) → ℤ) → ℤ → Bool)
    (hneg : ∀ J u a c, neg J u a c=true ↔ requestForm (fun i => v (requestIndices J u i)) a+c<0) :
    GoodRequestRows N v (requestUsingSigns (paperGrid N) neg) := by
  constructor
  intro J hJ
  let w := fun u => roundedFor (neg J u)
  exact knownRequestFamily_spec v Finset.univ J hJ (paperGrid N) (by unfold paperGrid; positivity) w
    (fun u => nativeGraphRowReducer J.card (w u)) (neg J) (hneg J)
    (fun u => (roundedFor_spec _ (neg J u) (hneg J u)).2)
    (fun u => nativeGraphRowReducer_correct.spec J.card (w u))

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
