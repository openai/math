import OAI.Computability.BorderVNP.ShortenPreparedPlacement
import OAI.Computability.BorderVNP.ShortenPreparedMean
import OAI.Computability.BorderVNP.ShortenPreparedMidpoints
import OAI.Computability.BorderVNP.ShortenEpochChoosePlaced
import OAI.Computability.BorderVNP.ShortenPlacedMeasurements

/-!
# The measured physical combining round

For every sufficiently long finite motion table we fix a depth floor and
two constants before choosing the fan-in or the networks. We choose a
single motion of each actual child, realize the canonical crossing, and
supply the exact geometric and count measurements for both rows of (6.3).
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Crossing Epoch Cover Cover.Frame Hecke Framed Packing PackMotions CombiningStep Filter Set
open scoped Classical Topology BorderVNP.Epoch.Cube

variable {D : ℕ} [NeZero D] {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
variable (B : PreparedBins D S h η) {K : Type*}

/-- A physical certificate for any particular labeled sample satisfying (6.2).
This form accepts the labels and the motion choices of the public reconstruction. -/
theorem eventually_measured_samples {ν : ℝ} (hh : 0 ≤ h) (hη : η ≤ ν/4) :
    ∀ᶠ n in atTop, ∃ l : ℕ, ∃ u : ℝ, 0 ≤ u ∧ ∀ d ≥ l, ∀ {k m : ℕ} (hk : 0 < k)
      {P : Type} {bits : P → ℕ} (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n)),
      let input := fun i => (child i).pack
      let active := fun i => (child i).active
      let sites := childSites child
      ∀ (L : Labels B input active sites)
        (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)
        (v : ℝ),
        Real.sqrt (Fintype.card (Cube D → Deck (d+1))) * Real.sqrt (binEnergy fun a =>
          SeedIntervals.count (parallelPacks input).layout (jointBin input (B.tag input active L.kind L.lift) ω) a / k -
          binMean input (B.tag (d := d+1) (n := n) input active L.kind L.lift) (sampleProb (d+1) n) a) ≤
          v * PlacedStep.childMaximum child hk / Real.sqrt k →
        ∃ (g : Placement (m := m) (parallelPacks input)
          (jointBin input (B.tag input active L.kind L.lift) ω)
          (CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart)
          (Cube D) (SurfaceHost (Cube D) (d+1))),
        g.old = movedOld input ω sites ∧
        g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart ∧
        g.project = (fun a => tileProject a.1) ∧
        Nonempty (PlacedStep.Measurements (B.placedStep child L ω g) hk h ν u v) := by
  obtain ⟨δ,hδ,hmin⟩ := B.exists_minLength
  obtain ⟨l₀,hsample⟩ := eventually_length (I := Cube D) (2*h) (by linarith)
  filter_upwards [B.eventually_fitted (K := K) hh hη] with n fitted
  obtain ⟨l₁,fit⟩ := fitted
  refine ⟨max l₀ l₁,δ⁻¹,(inv_pos.mpr hδ).le,?_⟩
  intro d hd k m hk P bits child input active sites L ω v dev
  obtain ⟨g,hold,hchart,hproject,hfits,half⟩ :=
    fit d (by omega) (m := m) input active sites L ω
  let step := B.placedStep child L ω g
  obtain ⟨oldMid,addr,midpoint,center⟩ := B.physical_midpoints input active sites L ω g hold hchart hproject
  have hlen (w : Active input active) (s : PackSample (lattice 1) elliptic (Cube D) (d+1) n) :
      dist (sampleMove s (sites w.1 ((input w.1).layout.src w.2.val)))
        (sampleMove s (sites w.1 ((input w.1).layout.dst w.2.val))) = B.length (L.kind w) := by
    rw [← L.src w,← L.dst w]
    exact hsample (d+1) (by omega) n _ _ _
      (mul_le_mul_of_nonneg_left (B.short _ (L.kind w).property) (by norm_num))
  have norm := B.tag_mean_norm input active L.kind L.lift hδ hmin sites ω hlen
  let mean := binMean input (B.tag (d := d+1) (n := n) input active L.kind L.lift) (sampleProb (d+1) n)
  have hi : g.input (parallelPacks input) step.bin step.perm =
      chargedLength (parallelPacks input).layout (movedOld input ω sites) (fun c => (step.bin c).isSome) :=
    congrArg (fun z => chargedLength (parallelPacks input).layout z (fun c => (step.bin c).isSome)) hold
  refine ⟨g,hold,hchart,hproject,⟨{
    mean := mean
    oldMid := oldMid
    addr := addr
    keeps := B.keeps_length child L ω g hchart
    fits := hfits
    midpoint := midpoint
    center := center
    half := half
    norm := ?_
    deviation := dev
  }⟩⟩
  exact norm.trans_eq (congrArg (fun z : ℝ => δ⁻¹*(z/k)) hi.symm)

/-- The fixed cutoffs and quantitative factors for a whole physical K-way step.
Each output is the concrete placement in the public prepared charts, and its
certified measurements refer to that very placement. -/
theorem eventually_measured {ν : ℝ} (hh : 0 ≤ h) (hη : η ≤ ν/4) :
    ∀ᶠ n in atTop, ∃ l : ℕ, ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ ∀ d ≥ l, ∀ {k m : ℕ} (hk : 0 < k)
      {P : Type} {bits : P → ℕ} (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n)),
      (∀ i w, Catalog.relative (d+2*n) ((child i).site w) ∈ S) →
      (∀ i c, (child i).charged c = true →
        dist ((child i).site ((child i).pack.layout.src c)) ((child i).site ((child i).pack.layout.dst c)) ≤ 2*h) →
      (∀ i c, (child i).active c = true →
        dist ((child i).midpoint c) ((child i).site ((child i).pack.layout.src c)) ≤
          dist ((child i).site ((child i).pack.layout.src c)) ((child i).site ((child i).pack.layout.dst c))/2) →
      let input := fun i => (child i).pack
      let active := fun i => (child i).active
      let sites := childSites child
      ∃ (L : Labels B input active sites)
        (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)
        (g : Placement (m := m) (parallelPacks input)
          (jointBin input (B.tag input active L.kind L.lift) ω)
          (CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart)
          (Cube D) (SurfaceHost (Cube D) (d+1))),
        g.old = movedOld input ω sites ∧
        g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart ∧
        g.project = (fun a => tileProject a.1) ∧
        Nonempty (PlacedStep.Measurements (B.placedStep child L ω g) hk h ν u v) := by
  filter_upwards [B.eventually_measured_samples (K := K) hh hη] with n sample
  obtain ⟨l₁,u,hu,cert⟩ := sample
  obtain ⟨N,choose⟩ := B.choose_child_samples n
  refine ⟨max 1 l₁,u,N,hu,Nat.cast_nonneg _,?_⟩
  intro d hd k m hk P bits child hc hshort hmid input active sites
  cases d with
  | zero => omega
  | succ d =>
    have : NeZero k := ⟨Nat.ne_of_gt hk⟩
    obtain ⟨L⟩ := B.exists_childLabels child hc hshort
    let X := PlacedStep.childMaximum child hk
    have hX (i : Fin k) : (child i).concentration ≤ X := Finset.le_sup' (s := (Finset.univ : Finset (Fin k)))
      (fun i => (child i).concentration) (Finset.mem_univ i)
    obtain ⟨ω,dev⟩ := choose d child L hmid X (((child ⟨0,hk⟩).nonneg.2).trans (hX ⟨0,hk⟩)) hX
    exact ⟨L,ω,cert (d+1) (by omega) hk child L ω N dev⟩

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
