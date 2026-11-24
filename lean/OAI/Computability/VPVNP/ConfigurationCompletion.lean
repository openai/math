import OAI.Computability.VPVNP.ConfigurationClosure
import OAI.Computability.VPVNP.GrassmannCompactness
import Mathlib.Topology.MetricSpace.Completion

/-!
# Realizable configurations in completions and limits of rescaled arrays

In Corollary 2.5 and Lemma 4.1 of *VP and VNP differ over every field*,
realizability of finite configurations passes to the metric completion.
Corollary 5.2 uses the same closedness to turn failure to realize the
distances of a cube into uniform exclusion over a class of metric spaces.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor.RealizableUpToScale

open Filter Set
open scoped Topology

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι]

/-- The coordinatewise closed set of realizable distance matrices on a
fixed finite label set. -/
theorem isClosed : IsClosed {d : ι → ι → ℝ | RealizableUpToScale k d} :=
  IsSeqClosed.isClosed fun x _ hx hlim ↦ RealizableUpToScale.limit x hx
    fun i j ↦ tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim i) j

/-- Realizability of every finite configuration passes from a pseudometric
space to its metric completion. -/
theorem completion {X : Type*} [PseudoMetricSpace X]
    (hX : ∀ y : ι → X, RealizableUpToScale k (fun i j ↦ dist (y i) (y j)))
    (z : ι → UniformSpace.Completion X) :
    RealizableUpToScale k (fun i j ↦ dist (z i) (z j)) := by
  let D (w : ι → UniformSpace.Completion X) := fun i j ↦ dist (w i) (w j)
  have hc : Continuous D := continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply i).dist (continuous_apply j)
  let embed (y : ι → X) : ι → UniformSpace.Completion X := fun i ↦ ↑(y i)
  have hdense : DenseRange embed :=
    DenseRange.piMap (fun _ : ι ↦ UniformSpace.Completion.denseRange_coe (α := X))
  refine hdense.induction_on (p := fun w ↦ RealizableUpToScale k (D w)) z
    (isClosed.preimage hc) ?_
  intro y
  simpa only [D, embed, UniformSpace.Completion.dist_eq] using hX y

/-- A class of spaces whose finite configurations are realizable uniformly
excludes any distance matrix which fails realizability, allowing arbitrary
positive rescalings of the marked configurations. -/
theorem notMem_closure_markedDistances {κ : Type*} (X : κ → Type*)
    [∀ j, PseudoMetricSpace (X j)]
    (hX : ∀ (j : κ) (y : ι → X j), RealizableUpToScale k (fun a b ↦ dist (y a) (y b)))
    {d : ι → ι → ℝ} (hd : ¬ RealizableUpToScale k d) :
    d ∉ closure (VPVNP.Grassmann.markedDistances X ι) := by
  intro hm
  apply hd
  refine closure_minimal (t := {D : ι → ι → ℝ | RealizableUpToScale k D}) ?_ isClosed hm
  rintro _ ⟨j, scale, hscale, y, rfl⟩
  exact (hX j y).smul hscale

end WireTensor.RealizableUpToScale

end VPVNP
end Computability
end OAI
