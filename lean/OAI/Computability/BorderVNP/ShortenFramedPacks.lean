import OAI.Computability.BorderVNP.ShortenFramedEndpoints
import OAI.Computability.BorderVNP.ShortenPackCatalogMean

/-!
# Canonical placement and actual bin tags of a parallel pack

The source catalog records both lifts of each active input cable, using one
common integral translation for the two ends. The same sampled motion is
applied to all sites of a copy. The resulting physical placement is indexed
by exactly the bins appearing in the rational Hecke and deck mean.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Framed

open Cover BorderVNP.Cover.Frame Hecke Epoch Crossing Packing PackMotions
open scoped Classical

variable {D copies d n : ℕ} {P S : Type} {bits : P → ℕ} {K : Type*}
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (kind : Active input active → S) (shape : Active input active → Catalog.SegmentType (Cube D))
    (b : Active input active → Cube D → gamma 1)
    (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) d n)

/-- Physical segment records for the disjoint union of all copies with their individually
chosen whole-pack motions. -/
noncomputable def parallelData (c : (parallelPacks input).layout.Edge) :
    Option (CanonicalPlacement.Segment (Cube D → Deck d) S (relativeWindow (Cube D))) :=
  if h : active c.1 c.2 then
    let w : Active input active := ⟨c.1,c.2,h⟩
    some (record (shape w) (kind w) (b w) (ω c.1))
  else none

/-- The canonical bin of each cable in the parallel network is the exact sampled
bin counted by the arithmetic Hecke/deck mean. -/
theorem parallel_bin (r : S → ℝ) {η : ℝ} (C : ∀ s, BinChart D (relativeWindow (Cube D)) (r s) η) :
    CanonicalPlacement.bin r C (parallelPacks input) (parallelData input active kind shape b ω) =
      jointBin input (sampledBin input active (speed ∘ shape)
        (fun w x => (⟨kind w,(C (kind w)).code x⟩ : Σ k, Fin (C k).bins))
        (fun w => sourceFrame (shape w) (b w)) (fun w => movedCarry (shape w) (b w))) ω := by
  funext c
  by_cases hc : active c.1 c.2
  · simp [CanonicalPlacement.bin,parallelData,jointBin,sampledBin,hc]
    rfl
  · simp [CanonicalPlacement.bin,parallelData,jointBin,sampledBin,hc]

/-- The selected pack samples applied to the original sites of the input copies. -/
noncomputable def movedOld (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n))
    (v : (parallelPacks input).layout.Site) : SurfaceHost (Cube D) d :=
  sampleMove (ω v.1) (sites v.1 v.2)

/-- On sufficiently deep covers the chart records of all copies realize the actual moved
sites and preserve true quotient lengths. The depth threshold is selected before the
motion words, deck labels, catalog, and network. -/
theorem parallel_realizes (R : ℝ) (hR : 0 ≤ R) :
    ∃ l, ∀ d ≥ l, ∀ n copies {P : Type} {bits : P → ℕ} (input : Fin copies → Pack D P bits K)
      (active : ∀ i, (input i).layout.Edge → Bool)
      (kind : Active input active → S) (shape : Active input active → Catalog.SegmentType (Cube D))
      (b : Active input active → Cube D → gamma 1) (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) d n)
      (r : S → ℝ) (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n)),
      (∀ w, (shape w).radius = r (kind w)) → (∀ w, 2*(shape w).radius ≤ R) →
      (∀ w : Active input active, productProjection _ (translatePoint (b w) (shape w).ends.1) =
        sites w.1 ((input w.1).layout.src w.2.val)) →
      (∀ w : Active input active, productProjection _ (translatePoint (b w) (shape w).ends.2) =
        sites w.1 ((input w.1).layout.dst w.2.val)) →
      CanonicalPlacement.Realizes r (parallelPacks input) (parallelData input active kind shape b ω)
        (movedOld input ω sites) (tileProject (d := d)) := by
  obtain ⟨l,hl⟩ := eventually_length (I := Cube D) R hR
  refine ⟨l,?_⟩
  intro d hd n copies P bits input active kind shape b ω r sites hk hr hs ht
  have get {c : (parallelPacks input).layout.Edge} {y}
      (hy : parallelData input active kind shape b ω c = some y) :
      ∃ h : active c.1 c.2, let w : Active input active := ⟨c.1,c.2,h⟩
        y = record (shape w) (kind w) (b w) (ω c.1) := by
    by_cases h : active c.1 c.2
    · exact ⟨h,(Option.some.inj (by simpa [parallelData,h] using hy)).symm⟩
    · simp [parallelData,h] at hy
  constructor
  · intro c y hy
    obtain ⟨h,rfl⟩ := get hy
    let w : Active input active := ⟨c.1,c.2,h⟩
    have he := projects (shape w) (kind w) (b w) (ω c.1) true
    simp only [ite_true] at he
    rw [hs w] at he
    change tileProject _ (endpoint _ _ (r (kind w)) true) = _
    rw [← hk w]
    exact he
  · intro c y hy
    obtain ⟨h,rfl⟩ := get hy
    let w : Active input active := ⟨c.1,c.2,h⟩
    have he := projects (shape w) (kind w) (b w) (ω c.1) false
    simp only [Bool.false_eq_true,ite_false] at he
    rw [ht w] at he
    change tileProject _ (endpoint _ _ (r (kind w)) false) = _
    rw [← hk w]
    exact he
  · intro c y hy
    obtain ⟨h,rfl⟩ := get hy
    let w : Active input active := ⟨c.1,c.2,h⟩
    have he := hl d hd n (shape w) (b w) (ω c.1) (hr w)
    rw [hs w,ht w,hk w] at he
    exact he

end Shortening.Framed

end BorderVNP
end Computability
end OAI
