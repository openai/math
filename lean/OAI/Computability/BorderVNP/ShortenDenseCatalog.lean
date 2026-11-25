import OAI.Computability.BorderVNP.PackedHistoryDenseStep
import OAI.Computability.BorderVNP.ShortenPreparedCatalog
import OAI.Computability.BorderVNP.ShortenCatalogProgram
import OAI.Computability.BorderVNP.ShortenCubeEnumeration

/-!
# Successor catalog for interval allocation in the public dense order

The merged cables are reindexed by their stable public slots before intervals
are allocated. The actual profile inserted on these selected endpoints has
the finite canonical site catalog and preserves the same short-radius cap.
The proof tracks retained sites through their original whole-pack motion
and installed sites through the local projection of their own seed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Crossing Epoch Cover Cover.Frame Framed Packing PackMotions CombiningStep
open BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

variable {D m d k n : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
    {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
    (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))
    (s : Stage m B.Bin d child)
    (ω : Fin k → Hecke.PackSample (lattice 1) elliptic (Cube D) (d+1) n)

private theorem projection_levelCast {I : Type} {a l : ℕ} (hl : a = l) (x : HyperbolicHost I) :
    levelCast hl (productProjection a x) = productProjection l x := by cases hl; rfl

/-- The dense directory preserves the actual positions of old sites. Thus each
retained site uses its original word number, even when its incident cables
have different sorted ordinals in the merged pack. -/
noncomputable def densePublicPlacement (sitesMem : ∀ i v, Catalog.relative (d+2*n) ((child i).site v) ∈ S)
    (hold : s.placed.old = movedOld (fun i => (child i).pack) ω (childSites child))
    (hchart : s.placed.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart)
    (hproject : s.placed.project = fun a => tileProject a.1) :
    Catalog.PublicPlacement (publicPattern (fun t : B.types => t.val.radius) B.chart n) S
      s.input s.label s.perm d s.placed := by
  let r := fun t : B.types => t.val.radius
  choose lifts hlifts hmem using fun i => exists_catalog_site_lifts (d+2*n) S ((child i).site) (sitesMem i)
  have hl (i) (v : (child i).pack.layout.Site) : productProjection ((d+1)+2*n) (lifts i v) = childSites child i v := by
    change _ = levelCast (Nat.add_right_comm d (2*n) 1) ((child i).site v)
    rw [←hlifts i v,projection_levelCast]
  exact {
    copyMotion := fun v => publicMoveCode r B.chart n ((ω v.1).1,(ω v.1).2.1)
    oldLift := fun v => lifts v.1 v.2
    oldDeck := fun v => deckRep (ω v.1).2.2
    oldType := fun v => hmem v.1 v.2
    moved := fun v => by
      rw [hold]
      change sampleMove (ω v.1) (childSites child v.1 v.2) = _
      rw [←hl,publicMoveCode_perm,publicMoveCode_matrix]
      exact sampleMove_projection (ω v.1) (lifts v.1 v.2)
    code := seedCode r B.chart n
    chartEq := fun a => hchart ▸ (publicPattern_chart r B.chart a).symm
    deck := fun a => deckRep a.1
    projects := fun a z => by rw [hproject]; rfl }

/-- Each output profile in the publicly ordered interval allocation has all
its relative sites in the same finite successor catalog and all its charged
cables within the common cap. The tracked output center is its true quotient
midpoint on this very sewn network. -/
theorem dense_result_catalog (e : PaidIdentity K D m)
    (sitesMem : ∀ i v, Catalog.relative (d+2*n) ((child i).site v) ∈ S)
    (hold : s.placed.old = movedOld (fun i => (child i).pack) ω (childSites child))
    (hchart : s.placed.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart)
    (hproject : s.placed.project = fun a => tileProject a.1) {ν : ℝ} (hν : ν ≤ 4)
    (fits : s.placed.fits s.input s.label s.perm s.orient h ν) (q : s.Index e) :
    Catalog.PlacedAt (B.successorSites n e) h (s.result e q) := by
  let r := fun t : B.types => t.val.radius
  let pat := publicPattern r B.chart n
  let pub := B.densePublicPlacement child s ω sitesMem hold hchart hproject
  have sites := Catalog.actual_sites e s.input s.label s.perm s.orient d pat S s.placed q
    pub.copyMotion pub.oldLift pub.oldDeck pub.oldType pub.moved pub.code pub.chartEq pub.deck pub.projects
  have short (c : s.input.layout.Edge) (hc : (s.label c).isSome = true) :
      dist (s.placed.old (s.input.layout.src c)) (s.placed.old (s.input.layout.dst c)) ≤ 2*h := by
    obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hc
    rw [s.placed.bin_length c a ha]
    exact mul_le_mul_of_nonneg_left (fits.1 a).2 (by norm_num)
  have bound := preserved_wire_cap e s.input s.label s.perm s.orient s.placed hν fits short q
  refine ⟨sites,bound,?_⟩
  intro c _
  let out := s.result e q
  exact (surfaceMidpoint_dist (out.site (out.pack.layout.src c)) (out.site (out.pack.layout.dst c))).1.le

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
