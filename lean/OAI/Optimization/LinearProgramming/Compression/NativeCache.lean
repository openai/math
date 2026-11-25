import OAI.Optimization.LinearProgramming.Compression.MinorNative

/-! One cached vector of generator magnitudes followed by the requested magnitude serves
the epoch commitment and the request computation. An epoch query ignores the final entry
by inserting a zero coefficient immediately before its affine constant. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- Ignoring a cached extra magnitude preserves the exact Boolean response. -/
theorem requestMagnitudeNegative_pad_epoch {g : ℕ} (fuel k : ℕ) (mag : Fin (g+1) → ℚ)
    (hm : ∀ i, 0 < mag i) (a : Fin g → ℤ) (c : ℤ) :
    requestMagnitudeNegative fuel k mag (Fin.snoc a 0) c =
      requestMagnitudeNegative fuel k (fun i => mag i.castSucc) a c := by
  apply Bool.eq_iff_iff.mpr
  rw [requestMagnitudeNegative_correct fuel k mag hm,
    requestMagnitudeNegative_correct fuel k _ (fun i => hm i.castSucc)]
  simp only [requestForm,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,Int.cast_zero,
    zero_mul,add_zero]

/-- Insert zero just before the homogeneous row's constant coordinate. -/
def padEpochQuery {g : ℕ} (a : Fin (g+1) → ℤ) : Fin ((g+1)+1) → ℤ :=
  Fin.snoc (Fin.snoc (fun i : Fin g => a i.castSucc) 0) (a (Fin.last g))

/-- The rounding program gets exactly the same reply after this fixed row conversion. -/
theorem affineCommitReply_pad_epoch {g : ℕ} (fuel k : ℕ) (mag : Fin (g+1) → ℚ)
    (hm : ∀ i, 0 < mag i) (a : Fin (g+1) → ℤ) :
    affineCommitReply (requestMagnitudeNegative fuel k mag) (padEpochQuery a) =
      affineCommitReply (requestMagnitudeNegative fuel k (fun i => mag i.castSucc)) a := by
  simpa only [affineCommitReply,padEpochQuery,Fin.snoc_castSucc,Fin.snoc_last] using
    congrArg (!·) (requestMagnitudeNegative_pad_epoch fuel k mag hm (fun i => a i.castSucc) (a (Fin.last g)))

/-- Commitment evaluated through the same request-sized negative oracle as every graph row. -/
def sharedEpochCommit (N g : ℕ) (negative : (Fin (g+1) → ℤ) → ℤ → Bool) : Fin g → ℚ :=
  let M := epochFormBudget g (paperWidth N) (epochHeightFor N g)
  computeCommitWith M (Lattice.lllShortSelector M) (fun a c => negative (Fin.snoc a 0) c)

/-- Native arithmetic transition. Membership is supplied by the index lookup, and the
only oracle input has the single fixed dimension g+1. -/
def sharedMinorStep (N g : ℕ) (position : Option (Fin g))
    (negative : (Fin (g+1) → ℤ) → ℤ → Bool) : Option ℚ :=
  let gamma := sharedEpochCommit N g negative
  match position with
  | some j => some (gamma j)
  | none =>
    let M := ((g+1)+2)*(requestCutoff (g+1)+3)
    let w := computeCommitWith M (Lattice.lllShortSelector M) negative
    let r := nativeGraphRowReducer g w
    let row := runMinorRequest w (fun i => requestDecodeRow (r i)) negative (paperGrid N)
    row.map fun f => ∑ i, f.1 i * gamma i + f.2

/-- The rank of a stored generator in the precise order used for the native reduction. -/
def matrixMinorPosition {ι : Type*} [LinearOrder ι] (J : Finset ι) (u : ι) : Option (Fin J.card) :=
  if hu : u∈J then some ((J.orderIsoOfFin rfl).symm ⟨u,hu⟩) else none

variable {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)

/-- The physical table in canonical internal order, with the designated request last. -/
def matrixMinorCache (J : Finset (NonzeroPairMinor D E)) (u : NonzeroPairMinor D E)
    (i : Fin (J.card+1)) : ℚ := minorMagnitude D E (requestIndices J u i)

@[simp] theorem matrixMinorCache_castSucc (J : Finset (NonzeroPairMinor D E)) (u : NonzeroPairMinor D E)
    (i : Fin J.card) : matrixMinorCache D E J u i.castSucc = minorMagnitude D E (J.orderIsoOfFin rfl i).val := by
  simp [matrixMinorCache]

@[simp] theorem matrixMinorCache_last (J : Finset (NonzeroPairMinor D E)) (u : NonzeroPairMinor D E) :
    matrixMinorCache D E J u (Fin.last J.card) = minorMagnitude D E u := by simp [matrixMinorCache]

/-- Exact implementation equation, valid for every generator set and dimension. Both
LLL calls, the subsequent dyadic graph tests, and the generator commitment share this cache. -/
theorem matrixMinorRequest_eq_sharedStep (fuel : ℕ) (J : Finset (NonzeroPairMinor D E))
    (u : NonzeroPairMinor D E) : matrixMinorRequest D E fuel J u =
    sharedMinorStep n J.card (matrixMinorPosition J u)
      (requestMagnitudeNegative fuel (paperRadius n+7) (matrixMinorCache D E J u)) := by
  let cache := matrixMinorCache D E J u
  let k := paperRadius n+7
  let neg := requestMagnitudeNegative fuel k cache
  have hneg : (fun a c => neg (Fin.snoc a 0) c) =
      requestMagnitudeNegative fuel k (fun i : Fin J.card => minorMagnitude D E (J.orderIsoOfFin rfl i).val) := by
    funext a c
    simpa only [neg,cache,matrixMinorCache_castSucc] using
      requestMagnitudeNegative_pad_epoch fuel k cache (fun i => minorMagnitude_pos D E _) a c
  have hc (j : J) : matrixMinorCommit D E fuel J j =
      sharedEpochCommit n J.card neg ((J.orderIsoOfFin rfl).symm j) := by
    unfold sharedEpochCommit
    rw [hneg]
    rfl
  change evaluateMinorRequest (matrixMinorCommit D E fuel)
      (nativeMinorRequest fuel k (paperGrid n) (minorMagnitude D E)) J u =
      sharedMinorStep n J.card (matrixMinorPosition J u) neg
  by_cases hu : u∈J
  · simp only [evaluateMinorRequest,matrixMinorPosition,dite_eq_left hu,sharedMinorStep,hc]
  · simp only [evaluateMinorRequest,matrixMinorPosition,dite_eq_right hu,sharedMinorStep,hc,
      OrderIso.symm_apply_apply]
    rfl

end Compression
end LinearProgramming
end Optimization
end OAI
