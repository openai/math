import OAI.Computability.BorderVNP.ShortenCatalogBounds

/-!
# Preparing the next shortening round

The site's finite-type data, segment lengths, frames, and minimum positive
length are chosen from the previous catalog and its finite motions and
canonical crossings. They work for every pack size, every deep quotient,
and every histogram, including paths on which earlier selectors are cut.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Catalog

open Crossing Cover Epoch CombiningStep Set
open scoped Classical

variable {I : Type*} [Fintype I] {D m : ℕ} [NeZero D] {K : Type*} [Field K]
variable {P : Type*} {bits : P → ℕ} {A : Type} [Fintype A]

/-- Realization of the public finite motion and relative-bin table in a physical
combining step. Each old record and each new seed has its own tile address. -/
structure PublicPlacement (pat : Pattern I D) (initial : Finset (HyperbolicHost I))
    (p : Pack D P bits K) (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (d : ℕ) (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1))) where
  /-- Index of the chosen motion of the copy containing the site. -/
  copyMotion : p.layout.Site → Fin pat.moves
  /-- A lift of the old site in its own copy's tile. -/
  oldLift : p.layout.Site → HyperbolicHost I
  /-- Extra post-motion deck translation of that copy. -/
  oldDeck : p.layout.Site → I → gamma 1
  /-- Every old site's relative position is already catalogued. -/
  oldType : ∀ v, normalize (oldLift v) ∈ initial
  /-- The public motion takes the old lifted site to the displayed quotient position. -/
  moved : ∀ v, g.old v = productProjection (d+1) (translatePoint (oldDeck v)
    (motion (pat.perm (copyMotion v)) (pat.matrix (copyMotion v)) (oldLift v)))
  /-- Relative seed address, after stripping the absolute tile index. -/
  code : A → Fin pat.bins
  /-- The lifted chart is the chart of the prepared relative seed address. -/
  chartEq : ∀ a, g.chart a = pat.chart (code a)
  /-- Absolute tile containing the seed representative. -/
  deck : A → I → gamma 1
  /-- Inserting sites uses exactly the specified deck shift and quotient projection. -/
  projects : ∀ a z, g.project a z = productProjection (d+1) (translatePoint (deck a) z)

/-- The successor catalog and its positive lower length cutoff hold uniformly
through every actual histogram branch. All data in the conclusion are chosen
before the quotient level, fan-in, site records and histogram counts. -/
theorem prepared_step (pat : Pattern I D) (initial : Finset (HyperbolicHost I)) (e : PaidIdentity K D m)
    (L h ν : ℝ) (hν : 0 ≤ ν) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ V : Set (SegmentType I), V.Finite ∧ ∃ μ : ℝ, 0 < μ ∧
      ∀ {P : Type*} {bits : P → ℕ} {A : Type} [Fintype A]
        (p : Pack D P bits K) (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
        (positive : p.layout.Edge → Bool) (d : ℕ)
        (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1))),
        PublicPlacement pat initial p bin perm d g →
        (∀ c, (bin c).isSome = true → dist (g.old (p.layout.src c)) (g.old (p.layout.dst c)) ≤ L) →
        g.fits p bin perm positive h ν → ∀ q : Counts e p bin perm,
        let out := physical p bin perm e positive q
        let z := g.postSites p bin perm e positive q
        (∀ v : out.Site, relative d (z v) ∈ pat.nextSites e initial) ∧
        ∀ c : out.Edge, postMask p bin perm e positive q c = true →
          dist (z (out.src c)) (z (out.dst c)) ≤ R ∧
          (z (out.src c) ≠ z (out.dst c) → μ ≤ dist (z (out.src c)) (z (out.dst c)) ∧
            ∃ v ∈ V, Realizes (z (out.src c)) (z (out.dst c)) v.ends) := by
  obtain ⟨R,hR,wire⟩ := uniform_wire_length e pat L (ν/4*h)
  obtain ⟨V,hV,seg⟩ := finite_segments (pat.nextSites e initial).finite_toSet R
  obtain ⟨μ,hμ,hmin⟩ := minimum_length hV
  refine ⟨R,hR,V,hV,μ,hμ,?_⟩
  intro P bits A _ p bin perm positive d g data oldLen fits q out z
  have sites := actual_sites e p bin perm positive d pat initial g q data.copyMotion data.oldLift
    data.oldDeck data.oldType data.moved data.code data.chartEq data.deck data.projects
  have lengths := wire p bin perm positive g q data.code data.chartEq oldLen (fun a u =>
    (fits.2 a u).trans (mul_le_mul_of_nonneg_left (fits.1 a).2 (by positivity)))
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
