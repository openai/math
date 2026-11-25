import OAI.Computability.BorderVNP.ShortenFramedPacks
import OAI.Computability.BorderVNP.ShortenCatalogStep

/-!
# The sampled canonical placements implement the finite iteration pattern

The motion table is indexed by the permutation and Hecke words. The seed
table is indexed by the relative class and its bin. Neither table depends
on the output level, the number of input records, or the deck post-shift.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Framed

open Cover BorderVNP.Cover.Frame Hecke Epoch Crossing Packing PackMotions CombiningStep
open scoped Classical

variable {D n : ℕ} {S : Type} [Fintype S] (r : S → ℝ) {η : ℝ}
    (C : ∀ s, BinChart D (relativeWindow (Cube D)) (r s) η)

/-- Finite public pattern for one round of actual frame and canonical-bin motions. -/
noncomputable def publicPattern (n : ℕ) : Catalog.Pattern (Cube D) D := by
  let e := Fintype.equivFin ((s : S) × Fin (C s).bins)
  exact samplePattern (Cube D) D n _ (fun k => (C (e.symm k).1).seed (e.symm k).2)

/-- The canonical public motion number of a permutation and its component words. -/
noncomputable def publicMoveCode (n : ℕ) :
    (Equiv.Perm (Cube D) × ProductSample (lattice 1) elliptic (Cube D) n) ≃ Fin (publicPattern r C n).moves :=
  sampleNames (Cube D) n

/-- The motion at this number acts by the selected sample’s permutation. -/
theorem publicMoveCode_perm (u : Equiv.Perm (Cube D) × ProductSample (lattice 1) elliptic (Cube D) n) :
    (publicPattern r C n).perm (publicMoveCode r C n u) = u.1 := by
  exact congrArg Prod.fst ((sampleNames (Cube D) n).symm_apply_apply u)

/-- Its component matrices are exactly the words used in the sampled histogram. -/
theorem publicMoveCode_matrix (u : Equiv.Perm (Cube D) × ProductSample (lattice 1) elliptic (Cube D) n) :
    (publicPattern r C n).matrix (publicMoveCode r C n u) = wordMatrix u.2 := by
  exact congrArg (fun v => wordMatrix v.2) ((sampleNames (Cube D) n).symm_apply_apply u)

/-- The relative public seed name, with the absolute deck name removed. -/
noncomputable def seedCode (n : ℕ) {T : Type} (a : CanonicalPlacement.Address r C T) :
    Fin (publicPattern r C n).bins := Fintype.equivFin _ a.2

/-- The enumerated chart table is the canonical seed at this actual bin. -/
theorem publicPattern_chart {T : Type} (a : CanonicalPlacement.Address r C T) :
    (publicPattern r C n).chart (seedCode r C n a) = CanonicalPlacement.chart r C a := by
  let e := Fintype.equivFin ((s : S) × Fin (C s).bins)
  change (C (e.symm (e a.2)).1).seed (e.symm (e a.2)).2 = (C a.2.1).seed a.2.2
  rw [e.symm_apply_apply]

variable {copies d m : ℕ} [NeZero D] {P : Type} {bits : P → ℕ} {K : Type*} [Field K]
    (input : Fin copies → Pack D P bits K)
    (data : (parallelPacks input).layout.Edge → Option
      (CanonicalPlacement.Segment (Cube D → Deck (d+1)) S (relativeWindow (Cube D))))
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+1+2*n))
    (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) (d+1) n)

/-- Produce the public placement certificate needed by the catalog recursion, for any
physical placement built from the checked sampled sites and canonical seed projections. -/
noncomputable def publicPlacementForBin (bin : (parallelPacks input).layout.Edge →
    Option (CanonicalPlacement.Address r C (Cube D → Deck (d+1)))) (initial : Finset (HyperbolicHost (Cube D)))
    (lifts : ∀ i, (input i).layout.Site → HyperbolicHost (Cube D))
    (hlift : ∀ i v, productProjection (d+1+2*n) (lifts i v) = sites i v)
    (hcatalog : ∀ i v, Catalog.normalize (lifts i v) ∈ initial)
    (g : Placement (m := m) (parallelPacks input) bin
      (CanonicalPlacement.perm r C) (Cube D) (SurfaceHost (Cube D) (d+1)))
    (hold : g.old = movedOld input ω sites)
    (hchart : g.chart = CanonicalPlacement.chart r C)
    (hproject : g.project = fun a => tileProject a.1) :
    Catalog.PublicPlacement (publicPattern r C n) initial (parallelPacks input)
      bin (CanonicalPlacement.perm r C) d g := by
  exact
    { copyMotion := fun v => publicMoveCode r C n ((ω v.1).1,(ω v.1).2.1)
      oldLift := fun v => lifts v.1 v.2
      oldDeck := fun v => deckRep (ω v.1).2.2
      oldType := fun v => hcatalog v.1 v.2
      moved := fun v => by
        rw [hold]; change sampleMove (ω v.1) (sites v.1 v.2) = _
        rw [← hlift v.1 v.2]
        rw [publicMoveCode_perm,publicMoveCode_matrix]
        exact sampleMove_projection (ω v.1) (lifts v.1 v.2)
      code := seedCode r C n
      chartEq := fun a => hchart ▸ (publicPattern_chart r C a).symm
      deck := fun a => deckRep a.1
      projects := fun a z => by rw [hproject]; rfl }

/-- Produce the public placement certificate needed by the catalog recursion, for any
physical placement built from the checked sampled sites and canonical seed projections. -/
noncomputable def publicPlacement (initial : Finset (HyperbolicHost (Cube D)))
    (lifts : ∀ i, (input i).layout.Site → HyperbolicHost (Cube D))
    (hlift : ∀ i v, productProjection (d+1+2*n) (lifts i v) = sites i v)
    (hcatalog : ∀ i v, Catalog.normalize (lifts i v) ∈ initial)
    (g : Placement (m := m) (parallelPacks input) (CanonicalPlacement.bin r C (parallelPacks input) data)
      (CanonicalPlacement.perm r C) (Cube D) (SurfaceHost (Cube D) (d+1)))
    (hold : g.old = movedOld input ω sites)
    (hchart : g.chart = CanonicalPlacement.chart r C)
    (hproject : g.project = fun a => tileProject a.1) :
    Catalog.PublicPlacement (publicPattern r C n) initial (parallelPacks input)
      (CanonicalPlacement.bin r C (parallelPacks input) data) (CanonicalPlacement.perm r C) d g :=
  publicPlacementForBin r C input sites ω _ initial lifts hlift hcatalog g hold hchart hproject

/-- An actual quotient site always has a lift. -/
theorem exists_site_lift {I : Type*} (d : ℕ) (x : SurfaceHost I d) :
    ∃ z : HyperbolicHost I, productProjection d z = x := by
  let z : HyperbolicHost I := WithLp.toLp 2 fun i => (x i).out
  refine ⟨z,?_⟩
  ext1 i
  exact Quotient.out_eq (x i)

/-- An input site's relative membership supplies the lifted membership used by
`publicPlacement`, for a single simultaneous choice on all retained sites. -/
theorem exists_catalog_site_lifts {I V : Type*} (d : ℕ)
    (initial : Finset (HyperbolicHost I)) (x : V → SurfaceHost I (d+1))
    (h : ∀ v, Catalog.relative d (x v) ∈ initial) :
    ∃ z : V → HyperbolicHost I, (∀ v, productProjection (d+1) (z v) = x v) ∧
      ∀ v, Catalog.normalize (z v) ∈ initial := by
  choose z hz using fun v => exists_site_lift (d+1) (x v)
  exact ⟨z,hz,fun v => by rw [← Catalog.relative_projection d,hz]; exact h v⟩

end Shortening.Framed

end BorderVNP
end Computability
end OAI
