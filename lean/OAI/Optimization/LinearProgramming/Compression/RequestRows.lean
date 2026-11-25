import OAI.Optimization.LinearProgramming.Compression.AdaptiveRequests
import OAI.Optimization.LinearProgramming.Compression.RequestProxy

/-! The truthful family of local affine rows produced by the graph-lattice request
supplies the hypotheses used for the online common extension. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

theorem latticeRequestRaw_goodRequestRows (reduce : GraphRowReducer)
    (hreduce : CorrectGraphRowReducer reduce) (N fuel k : ℕ) (mag : ι → ℚ)
    (hm : ∀ i, 0 < mag i) :
    GoodRequestRows N (fun i => requestMagnitudeProxy fuel k (mag i))
      (latticeRequestRaw reduce fuel k (paperGrid N) mag) := by
  constructor
  intro J hJ
  exact latticeRequestRaw_family reduce hreduce fuel k _ (by unfold paperGrid; positivity)
    mag hm Finset.univ J hJ

end Compression
end LinearProgramming
end Optimization
end OAI
