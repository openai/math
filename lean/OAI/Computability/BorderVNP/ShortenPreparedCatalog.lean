import OAI.Computability.BorderVNP.ShortenPreparedChildren
import OAI.Computability.BorderVNP.ShortenFramedPublicPlacement
import OAI.Computability.BorderVNP.ShortenCatalogFixed

/-!
# The finite successor catalog of the sampled physical children

The next relative site set depends on the word cutoff, the canonical seed
charts and the paid identity. It is valid for every input pack and every
attained joint histogram at every level. All output wires satisfy the same
short-wire cap used to construct the input charts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Cover Cover.Frame Hecke Epoch Framed Crossing PackMotions CombiningStep Packing
open scoped Classical

variable {D m d n k : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
    {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)

/-- The prepared bins determine the relative sites for the following round before
the level, fan-in, children or selector values are specified. -/
noncomputable def successorSites (n : ℕ) (e : PaidIdentity K D m) : Finset (HyperbolicHost (Cube D)) :=
  (publicPattern (fun t : B.types => t.val.radius) B.chart n).nextSites e S

variable (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)
    (g : Placement (m := m) (parallelPacks fun i => (child i).pack)
      (jointBin (fun i => (child i).pack)
        (B.tag (d := d+1) (n := n) (fun i => (child i).pack) (fun i => (child i).active) L.kind L.lift) ω)
      (CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart) (Cube D) (SurfaceHost (Cube D) (d+1)))

private theorem cast_projection {I : Type} {a l : ℕ} (hl : a = l) (x : HyperbolicHost I) :
    levelCast hl (productProjection a x) = productProjection l x := by cases hl; rfl

private theorem result_bounds {a l k : ℕ} {I : Type} [Fintype I] [inst : DecidableEq I] {A : Type} [Fintype A]
    (children : Fin k → PlacedPack D P bits K I l)
    (s : PlacedStep m A a children) (e : PaidIdentity K D m) (q : s.Index e)
    (next : Finset (HyperbolicHost I)) (cap : ℝ) :
    let p := parallelPacks (fun i => (children i).pack)
    let N := physical p s.bin s.perm e s.positive q
    let site := s.placed.postSites p s.bin s.perm e s.positive q
    (∀ v : N.Site, Catalog.relative a (site v) ∈ next) →
    (∀ c : N.Edge, postMask p s.bin s.perm e s.positive q c = true →
      dist (site (N.src c)) (site (N.dst c)) ≤ cap) →
    let out := s.result e q
    (∀ v, Catalog.relative a (out.site v) ∈ next) ∧
      ∀ c, out.charged c = true → dist (out.site (out.pack.layout.src c)) (out.site (out.pack.layout.dst c)) ≤ cap := by
  have he : inst = (fun _ _ => Classical.propDecidable _) := Subsingleton.elim _ _
  subst inst
  intro p N site sites lens out
  dsimp only [out,PlacedStep.result,CombiningStep.output,seedOutput]
  dsimp only [site,N,p,physical,sewnProfile] at sites lens
  exact ⟨sites,lens⟩

set_option maxHeartbeats 1600000 in
/-- The finite catalog and fixed length cap of every physical output of the prepared step. -/
theorem result_catalog (e : PaidIdentity K D m)
    (sitesMem : ∀ i v, Catalog.relative (d+2*n) ((child i).site v) ∈ S)
    (hold : g.old = movedOld (fun i => (child i).pack) ω (childSites child))
    (hchart : g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart)
    (hproject : g.project = fun a => tileProject a.1) {ν : ℝ} (hν : ν ≤ 4)
    (fits : g.fits _ _ _ (fun _ => true) h ν) (q : (B.placedStep child L ω g).Index e) :
    let out := (B.placedStep child L ω g).result e q
    (∀ v, Catalog.relative d (out.site v) ∈ B.successorSites n e) ∧
    ∀ c, out.charged c = true → dist (out.site (out.pack.layout.src c)) (out.site (out.pack.layout.dst c)) ≤ 2*h := by
  intro out
  let input := fun i => (child i).pack
  let step := B.placedStep child L ω g
  let r := fun t : B.types => t.val.radius
  let pat := publicPattern r B.chart n
  choose lifts hlifts hmem using fun i => exists_catalog_site_lifts (d+2*n) S ((child i).site) (sitesMem i)
  have hl (i) (v : (child i).pack.layout.Site) :
      productProjection ((d+1)+2*n) (lifts i v) = childSites child i v := by
    change _ = levelCast (Nat.add_right_comm d (2*n) 1) ((child i).site v)
    rw [← hlifts i v,cast_projection]
  let pub := publicPlacementForBin r B.chart input (childSites child) ω step.bin S lifts hl hmem g hold hchart hproject
  have sites := Catalog.actual_sites e (parallelPacks input) step.bin step.perm step.positive d pat S g q
    pub.copyMotion pub.oldLift pub.oldDeck pub.oldType pub.moved pub.code pub.chartEq pub.deck pub.projects
  have short (c : (parallelPacks input).layout.Edge) (hc : (step.bin c).isSome = true) :
      dist (g.old ((parallelPacks input).layout.src c)) (g.old ((parallelPacks input).layout.dst c)) ≤ 2*h := by
    cases hb : step.bin c with
    | none => simp [hb] at hc
    | some a =>
      rw [g.bin_length c a hb]
      exact mul_le_mul_of_nonneg_left (fits.1 a).2 (by norm_num)
  exact result_bounds child step e q (pat.nextSites e S) (2*h) sites
    (preserved_wire_cap e (parallelPacks input) step.bin step.perm step.positive g hν fits short q)

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
