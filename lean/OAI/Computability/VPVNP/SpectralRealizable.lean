import OAI.Computability.VPVNP.WireSpectrum

/-!
# Finite configurations of spectral wire distances

A configuration of labelled points is realized up to scale when the distances
between labels are a single positive multiple of their distances in a spectral
wire pseudometric. Several labels may designate the same tensor party.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

/-- The data realizing a matrix of distances by finitely many tensor parties.
The ambient party set has at least two members, as in Section 2. -/
structure WireRealization (k : Type*) [Field k] {ι : Type*} (d : ι → ι → ℝ) where
  /-- Finite ambient party set, with at least two members, carrying the wire metric of the
  realization. -/
  Parties : Type
  [finiteParties : Fintype Parties]
  [nontrivialParties : Nontrivial Parties]
  /-- Spectral point that assigns the wire distance between ambient tensor parties. -/
  spectrum : SpectralPoint k Parties
  /-- Party representing each label of the given configuration. Labels may share a party. -/
  label : ι → Parties
  /-- Positive factor multiplying the spectral wire distances to recover the given labelled
  distances. -/
  scale : ℝ
  scale_pos : 0 < scale
  distances : ∀ i j, d i j = scale * spectrum.wireDistance (label i) (label j)

attribute [instance] WireRealization.finiteParties WireRealization.nontrivialParties

/-- Realizability up to a common positive scale, in the sense of Section 2.2. -/
def RealizableUpToScale (k : Type*) [Field k] {ι : Type*} (d : ι → ι → ℝ) : Prop :=
  Nonempty (WireRealization k d)

/-- Restrict or repeat any of the labels in a realized configuration. -/
theorem RealizableUpToScale.relabel {k ι μ : Type*} [Field k] {d : ι → ι → ℝ}
    (h : RealizableUpToScale k d) (f : μ → ι) :
    RealizableUpToScale k (fun i j => d (f i) (f j)) := by
  obtain ⟨w⟩ := h
  exact ⟨{ Parties := w.Parties, spectrum := w.spectrum, label := w.label ∘ f,
           scale := w.scale, scale_pos := w.scale_pos, distances := fun i j => w.distances _ _ }⟩

/-- The choice of units for the distance matrix does not affect realizability. -/
theorem RealizableUpToScale.smul {k ι : Type*} [Field k] {d : ι → ι → ℝ}
    (h : RealizableUpToScale k d) {c : ℝ} (hc : 0 < c) :
    RealizableUpToScale k (fun i j => c * d i j) := by
  obtain ⟨w⟩ := h
  refine ⟨{ Parties := w.Parties, spectrum := w.spectrum, label := w.label,
            scale := c * w.scale, scale_pos := mul_pos hc w.scale_pos, distances := ?_ }⟩
  intro i j
  rw [w.distances, mul_assoc]

end WireTensor

end VPVNP
end Computability
end OAI
