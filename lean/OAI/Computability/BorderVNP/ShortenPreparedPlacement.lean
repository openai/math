import OAI.Computability.BorderVNP.ShortenCubeEnumeration
import OAI.Computability.BorderVNP.ShortenPreparedLabels

/-!
# Mean coverage of the actual physically fitted parallel pack

The preparation controls every sufficiently deep cover and every whole-pack
sample. Physical slots are classified with exactly the same bins whose
finite-sample means enter the first quantitative shortening estimate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Crossing Epoch Cover Cover.Frame Hecke Framed Packing PackMotions CombiningStep Set Filter
open scoped Classical Topology BorderVNP.Epoch.Cube

variable {D : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
variable (B : PreparedBins D S h η) {copies d n : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
variable (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
variable (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) d)

variable [NeZero D]

set_option maxHeartbeats 900000 in
/-- A word cutoff is chosen for the prepared catalog and a depth cutoff for the short
scale. For every finite input at these levels, the exact sampled-bin partition gives
a fitted physical placement and half coverage by the true mean, simultaneously for
all whole-pack samples. -/
theorem eventually_fitted {ν : ℝ} (hh : 0 ≤ h) (hη : η ≤ ν/4) :
    ∀ᶠ n in atTop, ∃ l, ∀ d ≥ l, ∀ {copies m : ℕ} {P : Type} {bits : P → ℕ}
      (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
      (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) ((d+1)+2*n))
      (L : Labels B input active sites) (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) (d+1) n),
      let mb := B.tag (d := d+1) (n := n) input active L.kind L.lift
      let bin := jointBin input mb ω
      let perm := CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart (T := Cube D → Deck (d+1))
      ∃ g : Placement (m := m) (parallelPacks input) bin perm (Cube D) (SurfaceHost (Cube D) (d+1)),
        g.old = movedOld input ω sites ∧
        g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart ∧
        g.project = (fun a => tileProject a.1) ∧
        g.fits (parallelPacks input) bin perm (fun _ => true) h ν ∧
        (g.input (parallelPacks input) bin perm / copies) / 2 ≤ matchedLength perm (fun a => 2*(g.chart a).radius)
          (binMean input mb (sampleProb (d+1) n)) := by
  have mix := eventually_catalog_half (D := D) (I := Cube D) (fun t : B.types => speed t.val)
    B.length (fun t => (B.chart t).code) (fun t => (B.chart t).perm) (fun t b => (B.regular t b).1)
    (fun t b => (B.regular t b).2) B.invariant (fun t => mul_nonneg (by norm_num) t.val.positive.le)
  obtain ⟨l,hl⟩ := eventually_length (I := Cube D) (2*h) (by linarith)
  obtain ⟨lR,hR⟩ := parallel_realizes (D := D) (K := K) (S := B.types) (2*h) (by linarith)
  filter_upwards [mix] with n hn
  refine ⟨max l lR,?_⟩
  intro d hd copies m P bits input active sites L ω mb bin perm
  let r := fun t : B.types => t.val.radius
  let shape := fun w : Active input active => (L.kind w).val
  let data := parallelData input active L.kind shape L.lift ω
  let old := movedOld input ω sites
  let p := parallelPacks input
  have hs (w : Active input active) : productProjection _ (translatePoint (L.lift w) (shape w).ends.1) =
      sites w.1 ((input w.1).layout.src w.2.val) := by
    exact L.src w
  have ht (w : Active input active) : productProjection _ (translatePoint (L.lift w) (shape w).ends.2) =
      sites w.1 ((input w.1).layout.dst w.2.val) := by
    exact L.dst w
  have short (w : Active input active) : 2*(shape w).radius ≤ 2*h :=
    mul_le_mul_of_nonneg_left (B.short _ (L.kind w).property) (by norm_num)
  have lens (w : Active input active) (s : PackSample (lattice 1) elliptic (Cube D) (d+1) n) :
      dist (sampleMove s (sites w.1 ((input w.1).layout.src w.2.val)))
        (sampleMove s (sites w.1 ((input w.1).layout.dst w.2.val))) = B.length (L.kind w) := by
    rw [←hs w,←ht w]
    exact hl (d+1) (by omega) n _ _ _ (short w)
  have re := hR (d+1) (by omega) n copies input active L.kind shape L.lift ω r sites (fun _ => rfl) short hs ht
  have hbin : CanonicalPlacement.bin r B.chart p data = bin :=
    parallel_bin input active L.kind shape L.lift ω r B.chart
  have fitted := CanonicalPlacement.exists_placement (m := m) r B.chart p data old tileProject
    tileProject_nonexpanding re (fun t => ⟨t.val.positive.le,B.short _ t.property⟩) hη
  rw [hbin] at fitted
  obtain ⟨g,hg,hc,hp,hfit⟩ := fitted
  refine ⟨g,hg,hc,hp,hfit,?_⟩
  have he := hn input active L.kind (d+1) (fun w => sourceFrame (shape w) (L.lift w))
    (fun w => movedCarry (shape w) (L.lift w)) (fun i s v => sampleMove s (sites i v)) ω lens
  let mean := binMean input mb (sampleProb (d+1) n)
  let leng : (Cube D → Deck (d+1)) × B.Bin → ℝ := catalogLength B.length (d+1)
  change chargedLength p.layout old (fun c => (bin c).isSome) / copies / 2 ≤ matchedLength perm leng mean at he
  have leftEq : g.input p bin perm = chargedLength p.layout old (fun c => (bin c).isSome) :=
    congrArg (fun place => chargedLength p.layout place (fun c => (bin c).isSome)) hg
  have rightEq : (fun a => 2*(g.chart a).radius) = leng :=
    congrArg (fun chart : (Cube D → Deck (d+1)) × B.Bin → SeedChart (Cube D) D =>
      fun a => 2*(chart a).radius) hc
  exact (congrArg (fun x : ℝ => x / copies / 2) leftEq).le.trans
    (he.trans_eq (congrArg (fun f => matchedLength perm f mean) rightEq.symm))

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
