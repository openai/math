import OAI.Computability.BorderVNP.ShortenPublicStageTrace
import OAI.Computability.BorderVNP.ShortenDenseCatalog
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseRecords

/-!
# Joint receipt for the actual public sorting and motion selection

For any decoded endpoint labels and any samples certified by the public
deviation test, the same installed sorted network carries the geometric
trace, quantitative row inputs, per-tile record bound and next catalog.
This holds uniformly before its fan-in, wire widths and quotient level
are supplied.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Crossing Epoch Cover Cover.Frame Hecke Framed Packing PackMotions CombiningStep Filter
open BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical Topology BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (e : PaidIdentity K D m)
variable {k d n rows : ℕ} {P : Type} {bits : P → ℕ}
    (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)
    (slot : (raw child).layout.Edge ↪ Fin rows)

/-- Evidence on one installed network for the exact source labels, Hecke
samples, and stable row names that produced it. -/
structure DenseReceipt (s : Stage m B.Bin d child) (hk : 0 < k) (H ν u v : ℝ) (C : ℕ) where
  /-- Public motion, old positions and canonical chart of this actual step. -/
  trace : B.DenseTrace child L ω slot s
  /-- Its physical row measurements at the common saving scale. -/
  measure : Stage.Measurements s hk H ν u v
  /-- One bound for all predecessor site payloads and all attained profiles. -/
  records : s.RecordFactor e C
  /-- Every actual output, including its midpoint positions, meets the successor catalog. -/
  closure : ∀ q : s.Index e, Catalog.PlacedAt (B.successorSites n e) h (s.result e q)

set_option maxHeartbeats 1400000 in
/-- After the catalog fixes the word cutoff, choose the depth, record and
mean constants once. Every computed sample satisfying (6.2) gives a joint
receipt on the sorted network, without choosing new labels or a new motion. -/
theorem eventually_dense_receipts {H ν θ : ℝ} (hm : 0 < m) (hh : 0 ≤ h) (hH : h ≤ H)
    (ht : 0 ≤ θ) (hθ : θ ≤ ν) (hsafe : θ ≤ 4) (hη : η ≤ θ/4) :
    ∀ᶠ n in atTop, ∃ floor C : ℕ, ∃ u : ℝ, 0 ≤ u ∧ 0 < floor ∧ ∀ d ≥ floor,
      ∀ {k rows : ℕ} (hk : 0 < k) {P : Type} {bits : P → ℕ}
      (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n)),
      (∀ i, Catalog.PlacedAt S h (child i)) →
      ∀ (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
      (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)
      (slot : (raw child).layout.Edge ↪ Fin rows) (v : ℝ), B.SampleDeviation child L ω hk v →
      ∃ s : Stage m B.Bin d child, Nonempty (B.DenseReceipt e child L ω slot s hk H ν u v C) := by
  filter_upwards [B.eventually_dense_samples (K := K) hh hη] with n install
  obtain ⟨l,u,hu,run⟩ := install
  obtain ⟨C,records⟩ := B.dense_result_localRecords e n hm hh ht
  refine ⟨max 1 l,C,u,hu,(by omega),?_⟩
  intro d hd k rows hk P bits child hchild L ω slot v dev
  obtain ⟨s,⟨trace⟩,⟨small⟩⟩ := run d ((le_max_right ..).trans hd) (m := m) hk child L ω slot v dev
  have moved : s.placed.old = movedOld (fun i => (child i).pack) ω (childSites child) := by
    rw [trace.realizes]; exact trace.moved
  have chart : s.placed.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart := by
    rw [trace.realizes]; exact trace.chart
  have project : s.placed.project = fun a => tileProject a.1 := by
    rw [trace.realizes]; exact trace.project
  let wide : Stage.Measurements s hk H ν u v :=
    {small with fits := s.placed.fits_mono s.input s.label s.perm s.orient hH hθ small.fits}
  exact ⟨s,⟨⟨trace,wide,records d (by omega) hk child s ω moved small,fun q =>
    B.dense_result_catalog child s ω e (fun i => (hchild i).sites) moved chart project hsafe small.fits q⟩⟩⟩

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
