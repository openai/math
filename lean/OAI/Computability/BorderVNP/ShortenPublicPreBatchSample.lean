import OAI.Computability.BorderVNP.ShortenPublicPreBatch
import OAI.Computability.BorderVNP.ShortenPreparedCatalog
import OAI.Computability.BorderVNP.ShortenPreparedDeckTransport

/-!
# Site reconstruction for the same selected geometric sample as the histogram

Use the actual permutation and Hecke words to index the finite pattern. The
forward deck translation multiplies all sites in that copy, and the seed
array enumerates the genuine product tile and relative chart bin. The site
table only reads occupied old slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Cover Cover.Frame Cover.AddressCircuit Hecke Epoch Catalog Framed Crossing CombiningStep Packing PackMotions
open PreparedBins PublicSegments
open scoped Classical

variable {D n m q copies d lev : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
variable (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
variable {M : Type} [DecidableEq M] (index : M ≃ PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)

/-- Relative site pattern used by this prepared segment catalog. -/
noncomputable abbrev sitePattern := publicPattern (fun t : B.types => t.val.radius) B.chart n

/-- The finite selector's candidate index in the site's canonical motion ordering. -/
noncomputable def candidateIndex : M ≃ Fin (sitePattern (n := n) B).moves :=
  index.trans (publicMoveCode (fun t : B.types => t.val.radius) B.chart n)

/-- Reading the selected candidate from the whole-pack sample uses the selector's own ordering. -/
noncomputable def sampledChoice {l : ℕ} (s : PackSample (lattice 1) elliptic (Cube D) l n) : M :=
  index.symm (s.1,s.2.1)

/-- Reindexing a quotient name changes only the expression for its integer depth. -/
def deckCast {a b : ℕ} (h : a=b) (x : Deck a) : Deck b := h ▸ x

private theorem deckCast_out {a b : ℕ} (h : a=b) (x : Deck a) :
    deckCast h x = (x.out : Deck b) := by
  cases h
  exact (QuotientGroup.out_eq' x).symm

private theorem projection_cast {I : Type} {a b : ℕ} (h : a=b) (x : HyperbolicHost I) :
    productProjection b x = levelCast h (productProjection a x) := by cases h; rfl

variable [NeZero D] {P : Type} {bits : P → ℕ} {K : Type*}
variable (input : Fin copies → Pack D P bits K)
variable (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (lev+1+2*n))
variable (active : ∀ i, (input i).layout.Edge → Bool) (L : Labels B input active sites)
variable (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) (lev+1) n)

set_option maxHeartbeats 1200000 in
/-- Site rows and histogram rows use the same labels and the same whole-pack
sample. Starting with only the actual raw site fields and selected motions,
the compiled preparation satisfies every occupied site and seed read of the
physical combining step. -/
theorem sampled_preFields_reads {V E k w seeds : ℕ} {Data : Type*} (hd : 1 ≤ d)
    (level : lev+1=d+2*n) (home : Fin V → Fin copies) (old : (parallelPacks input).layout.Site ↪ Fin V)
    (owner : ∀ v, home (old v) = v.1)
    (seed : ((Cube D → Deck (lev+1)) × B.Bin) ≃ Fin seeds)
    (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data) (raw : Raw Data V E k w → Bool)
    (lifts : ∀ i, (input i).layout.Site → HyperbolicHost (Cube D))
    (hlifts : ∀ i v, productProjection (lev+1+2*n) (lifts i v) = sites i v)
    (hmem : ∀ i v, normalize (lifts i v) ∈ S)
    (valid : ∀ (v : (parallelPacks input).layout.Site), relativeAt (d+2*n+2*n) (by omega)
      (levelCast (congrArg (·+2*n) level) (sites v.1 v.2)) ∈ S)
    (payload : ∀ (v : (parallelPacks input).layout.Site) j, raw (.inr (.inl (old v,field j))) =
      siteAtBits (by omega) (levelCast (congrArg (·+2*n) level) (sites v.1 v.2)) (valid v) j)
    (g : Placement (m := m) (parallelPacks input) (jointBin input (B.tag input active L.kind L.lift) ω)
      (CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart) (Cube D) (SurfaceHost (Cube D) (lev+1)))
    (hold : g.old = movedOld input ω sites)
    (hchart : g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart)
    (hproject : g.project = fun a => tileProject a.1) :
    let radius := fun t : B.types => t.val.radius
    let bin := jointBin input (B.tag input active L.kind L.lift) ω
    let perm := CanonicalPlacement.perm radius B.chart
    let pub := publicPlacementForBin radius B.chart input sites ω bin S lifts hlifts hmem g hold hchart hproject
    let choices := fun i => sampledChoice index (ω i)
    let shifts := fun i j => deckCast level ((ω i).2.2 j)
    let x := Sum.elim (motionWires enum choices shifts) raw
    PlacementReads (parallelPacks input) bin perm enum (sitePattern B) S home g pub old seed.toEmbedding
      (preFields enum (sitePattern B) (candidateIndex B index) field seed (seedCode radius B.chart n)
        (fun a i => deckCast level (a.1 i)) x) := by
  intro radius bin perm pub choices shifts x
  have lift (v : (parallelPacks input).layout.Site) : productProjection (d+2*n+2*n) (lifts v.1 v.2) =
      levelCast (congrArg (·+2*n) level) (sites v.1 v.2) := by
    rw [← hlifts v.1 v.2]
    exact projection_cast _ _
  apply preFields_reads enum (sitePattern B) (parallelPacks input) bin perm home g pub old seed
    (candidateIndex B index) field choices shifts _ _ raw (by change 0 < d+2*n+2*n; omega)
    (fun v => levelCast (congrArg (·+2*n) level) (sites v.1 v.2)) valid lift payload
  · intro v
    rw [owner]
    exact congrArg (publicMoveCode radius B.chart n) (index.apply_symm_apply ((ω v.1).1,(ω v.1).2.1))
  · intro v i
    rw [owner]
    exact deckCast_out level ((ω v.1).2.2 i)
  · intro s; rfl
  · intro s i
    exact deckCast_out level (s.1 i)

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
