import OAI.Computability.BorderVNP.ShortenDenseFitted
import OAI.Computability.BorderVNP.ShortenDenseMeasurements

/-!
# A publicly selected sample produces its own measured stable-order crossing

The labels and sample choices are inputs, as are the public sparse row
IDs. The witness returns the physical geometry for this very tuple. The
joint bin counts, means and old vertex motions are evaluated before
reordering; its output and hooks are the ones selected after reordering.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Crossing Epoch Cover Cover.Frame Hecke Framed Packing PackMotions CombiningStep Filter
open BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical Topology BorderVNP.Epoch.Cube

variable {D : ℕ} [NeZero D] {K : Type*} [Field K] {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η)
variable {k m d n rows : ℕ} {P : Type} {bits : P → ℕ}
    (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)

/-- The physical (6.2) test for the decoded endpoint labels and the selected
motions, in the exact true finite sample law used by the child count banks. -/
def SampleDeviation (hk : 0 < k) (v : ℝ) : Prop :=
  let input := fun i => (child i).pack
  let active := fun i => (child i).active
  Real.sqrt (Fintype.card (Cube D → Deck (d+1))) * Real.sqrt (binEnergy fun a =>
    SeedIntervals.count (raw child).layout (B.publicBin child L ω) a / k -
    binMean input (B.tag (d := d+1) (n := n) input active L.kind L.lift) (sampleProb (d+1) n) a) ≤
    v * PlacedStep.childMaximum child hk / Real.sqrt k

variable (slot : (raw child).layout.Edge ↪ Fin rows)

/-- The traced actual step for prescribed labels, samples and public cable
rows. Its bin function and all new slot attachments are those of the
canonical installation on the publicly sorted merged network. -/
structure DenseTrace (s : Stage m B.Bin d child) where
  /-- Canonical placement with endpoint lifts for this sorted interval allocation. -/
  geometry : B.DensePlacement child L ω slot m
  /-- The chosen physical network step is exactly the installation from these data. -/
  realizes : s = B.densePlacedStep child L ω slot geometry
  /-- The old sites are the actual selected whole-pack motions. -/
  moved : geometry.old = movedOld (fun i => (child i).pack) ω (childSites child)
  /-- The fixed chart lookup uses the selected relative bins. -/
  chart : geometry.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart
  /-- Every inserted site uses the canonical tile deck projection. -/
  project : geometry.project = fun a => tileProject a.1

omit [Field K] in
set_option maxHeartbeats 1200000 in
/-- Fixed-sample geometry and measured (6.3) inputs for any actual public
row order. Only the measured deviation of the prescribed samples is
required. The shape, wire-width selection and moves never depend on local
field entries. -/
theorem eventually_dense_samples {θ : ℝ} (hh : 0 ≤ h) (hη : η ≤ θ/4) :
    ∀ᶠ n in atTop, ∃ floor : ℕ, ∃ u : ℝ, 0 ≤ u ∧ ∀ d ≥ floor, ∀ {k m rows : ℕ} (hk : 0 < k)
      {P : Type} {bits : P → ℕ} (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))
      (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
      (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)
      (slot : (raw child).layout.Edge ↪ Fin rows) (v : ℝ), B.SampleDeviation child L ω hk v →
      ∃ s : Stage m B.Bin d child, Nonempty (B.DenseTrace child L ω slot s) ∧
        Nonempty (Stage.Measurements s hk h θ u v) := by
  obtain ⟨l₂,dense⟩ := B.dense_fitted (K := K) hh hη
  filter_upwards [B.eventually_measured_samples (K := K) hh hη] with n run
  obtain ⟨l₁,u,hu,measured⟩ := run
  refine ⟨max l₁ l₂,u,hu,?_⟩
  intro d hd k m rows hk P bits child L ω slot v dev
  obtain ⟨rawG,old₁,chart₁,proj₁,⟨M⟩⟩ := measured d ((le_max_left ..).trans hd) (m := m) hk child L ω v dev
  obtain ⟨g,old₂,chart₂,proj₂,fit⟩ := dense d ((le_max_right ..).trans hd) (m := m) child L ω slot
  let s := B.densePlacedStep child L ω slot g
  let r := B.placedStep child L ω rawG
  refine ⟨s,⟨⟨g,rfl,old₂,chart₂,proj₂⟩⟩,?_⟩
  exact Stage.measurements_dense s r M rfl rfl (old₂.trans old₁.symm) (chart₂.trans chart₁.symm)
    (proj₂.trans proj₁.symm) fit

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
