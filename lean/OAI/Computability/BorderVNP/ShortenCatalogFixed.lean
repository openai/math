import OAI.Computability.BorderVNP.ShortenWireCap

/-!
# A successor catalog at the fixed epoch cap

A charged input segment of length at most twice the chart scale produces
only charged segments obeying that very same cap. The finite successor
catalog and its positive minimum are selected uniformly at the fixed cap.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Catalog

open Crossing Cover Epoch CombiningStep Set
open scoped Classical

variable {I : Type*} [Fintype I] {D m : ℕ} [NeZero D] {K : Type*} [Field K]

/-- The successor catalog and its positive lower length cutoff hold uniformly
through every actual histogram branch. All data in the conclusion are chosen
before the quotient level, fan-in, site records and histogram counts. -/
theorem prepared_step_preserving_cap (pat : Pattern I D) (initial : Finset (HyperbolicHost I)) (e : PaidIdentity K D m)
    (h ν : ℝ) (hν : ν ≤ 4) :
    ∃ V : Set (SegmentType I), V.Finite ∧ ∃ μ : ℝ, 0 < μ ∧
      ∀ {P : Type*} {bits : P → ℕ} {A : Type} [Fintype A]
        (p : Pack D P bits K) (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
        (positive : p.layout.Edge → Bool) (d : ℕ)
        (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1))),
        PublicPlacement pat initial p bin perm d g →
        (∀ c, (bin c).isSome = true → dist (g.old (p.layout.src c)) (g.old (p.layout.dst c)) ≤ 2*h) →
        g.fits p bin perm positive h ν → ∀ q : Counts e p bin perm,
        let out := physical p bin perm e positive q
        let z := g.postSites p bin perm e positive q
        (∀ v : out.Site, relative d (z v) ∈ pat.nextSites e initial) ∧
        ∀ c : out.Edge, postMask p bin perm e positive q c = true →
          dist (z (out.src c)) (z (out.dst c)) ≤ 2*h ∧
          (z (out.src c) ≠ z (out.dst c) → μ ≤ dist (z (out.src c)) (z (out.dst c)) ∧
            ∃ v ∈ V, Realizes (z (out.src c)) (z (out.dst c)) v.ends) := by
  obtain ⟨V,hV,seg⟩ := finite_segments (pat.nextSites e initial).finite_toSet (2*h)
  obtain ⟨μ,hμ,hmin⟩ := minimum_length hV
  refine ⟨V,hV,μ,hμ,?_⟩
  intro P bits A _ p bin perm positive d g data oldLen fits q out z
  have sites := actual_sites e p bin perm positive d pat initial g q data.copyMotion data.oldLift
    data.oldDeck data.oldType data.moved data.code data.chartEq data.deck data.projects
  have lengths := preserved_wire_cap e p bin perm positive g hν fits oldLen q
  refine ⟨sites,?_⟩
  intro c hc
  have hlen := lengths c hc
  refine ⟨hlen,?_⟩
  intro hne
  obtain ⟨v,hv,hxy⟩ := seg d _ _ (sites (out.src c)) (sites (out.dst c)) hne hlen
  exact ⟨hmin d _ _ v hv hxy,v,hv,hxy⟩

end Shortening.Catalog

end BorderVNP
end Computability
end OAI
