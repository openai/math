import OAI.Computability.BorderVNP.ShortenDenseCatalog
import OAI.Computability.BorderVNP.ShortenPublicPreBatchSample
import OAI.Computability.BorderVNP.ShortenPublicRelativeCharged

/-!
# The site preparation reads for the actual stable-order allocator

Sorting cable numbers changes neither a child site's pack, nor its point.
The same canonical motion and seed table therefore give its full physical
placement contract at the input of the checked dense-order successor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Cover Cover.Frame Cover.AddressCircuit Hecke Epoch Catalog Framed Crossing CombiningStep Packing PackMotions
open PreparedBins PublicSegments BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

/-- Select a stored field at an equal circuit depth. This transports just its
wire name, so the same field is read for every branch of the physical stage. -/
def fieldAtLevel {Site I Data : Type*} {a b : ℕ} (h : a=b) (f : FieldBit Site I a → Data) :
    FieldBit Site I b → Data := h ▸ f

/-- The serialized predecessor table supplies the two raw-site obligations
of both the dense site mover and the classifier, even when the physical
depth and the circuit depth are expressed differently. -/
theorem SegmentReady.fields_atLevel {D V E w lev z : ℕ} {S : Finset (HyperbolicHost (Cube D))}
    {Data P : Type*} {bits : P → ℕ} {N : Network D P bits} {site : N.Site ↪ Fin V} {row : N.Edge ↪ Fin E}
    {dummy : Fin E → N.Site} {pos : N.Site → SurfaceHost (Cube D) (lev+1)}
    {field : FieldBit (↥S) (Cube D) (lev+1) → Data} {mask : N.Edge → Bool} {x : Raw Data V E w w → Bool}
    (ready : SegmentReady S N site row dummy pos field mask x) (level : lev+1=z) :
    ∃ valid : ∀ v, relativeAt z (by omega) (levelCast level (pos v)) ∈ S,
      ∀ v j, x (.inr (.inl (site v,fieldAtLevel level field j))) =
        siteAtBits (by omega) (levelCast level (pos v)) (valid v) j := by
  cases level
  exact ⟨ready.valid,ready.payload⟩

variable {D n t m q copies d lev V E k w seeds : ℕ} [NeZero D]
    {P : Type} {bits : P → ℕ} {K : Type*}
    {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
    (child : Fin copies → PlacedPack D P bits K (Cube D) (lev+2*n)) (s : Stage t B.Bin lev child)
    (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) (lev+1) n)
    (sitesMem : ∀ i v, relative (lev+2*n) ((child i).site v) ∈ S)
    (hold : s.placed.old = movedOld (fun i => (child i).pack) ω (childSites child))
    (hchart : s.placed.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart)
    (hproject : s.placed.project = fun a => tileProject a.1)

private theorem dense_lift (v : s.input.layout.Site) :
    productProjection (lev+2*n+1) ((B.densePublicPlacement child s ω sitesMem hold hchart hproject).oldLift v) =
      (child v.1).site v.2 :=
  (Classical.choose_spec (exists_catalog_site_lifts (lev+2*n) S ((child v.1).site) (sitesMem v.1))).1 v.2

private theorem projLevel {I : Type} {a b : ℕ} (h : a=b) (x : HyperbolicHost I) :
    productProjection b x = levelCast h (productProjection a x) := by cases h; rfl

/-- Identify the physical seed table with the circuit seed table, whose
level expression may be written differently. -/
def seedLevel {D a b : ℕ} {A : Type} (level : a=b) :
    ((Cube D → Deck a) × A) ≃ ((Cube D → Deck b) × A) := level ▸ Equiv.refl _

private theorem seedLevel_tile {D a b : ℕ} {A : Type} (level : a=b) (s : (Cube D → Deck a) × A) (i : Cube D) :
    (seedLevel level s).1 i = deckCast level (s.1 i) := by cases level; rfl

private theorem seedLevel_bin {D a b : ℕ} {A : Type} (level : a=b) (s : (Cube D → Deck a) × A) :
    (seedLevel level s).2 = s.2 := by cases level; rfl

private theorem deckCast_rep {a b : ℕ} (h : a=b) (x : Deck a) : deckCast h x = (x.out : Deck b) := by
  cases h
  exact (QuotientGroup.out_eq' x).symm

set_option maxHeartbeats 1800000 in
/-- The raw site fields of the actual children and their shared selected
motions realize the stable-order placement, including every empty seed and
without constraining the payload of unused site IDs. -/
theorem dense_preFields_reads (enum : Fin q ≃ Cube D)
    (index : Fin m ≃ PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)
    (hd : 1 ≤ d) (level : lev+1 = d+2*n) (home : Fin V → Fin copies) (old : s.input.layout.Site ↪ Fin V)
    (owner : ∀ v, home (old v) = v.1) (seed : ((Cube D → Deck (d+2*n)) × B.Bin) ≃ Fin seeds)
    {Data : Type*} (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data) (raw : Raw Data V E k w → Bool)
    (valid : ∀ v : s.input.layout.Site, relativeAt (d+2*n+2*n) (by omega)
      (levelCast (by omega) ((child v.1).site v.2)) ∈ S)
    (payload : ∀ (v : s.input.layout.Site) j, raw (.inr (.inl (old v,field j))) =
      siteAtBits (by omega) (levelCast (by omega) ((child v.1).site v.2)) (valid v) j) :
    let pat := sitePattern (n := n) B
    let physicalSeed := (seedLevel level).trans seed
    let radius := fun t : B.types => t.val.radius
    let pub := B.densePublicPlacement child s ω sitesMem hold hchart hproject
    let x := Sum.elim (motionWires enum (fun i => sampledChoice index (ω i))
      (fun i j => deckCast level ((ω i).2.2 j))) raw
    PlacementReads s.input s.label s.perm enum pat S home s.placed pub old physicalSeed.toEmbedding
      (preFields enum pat (candidateIndex B index) field seed (seedCode radius B.chart n) Prod.fst x) := by
  intro pat physicalSeed radius pub x
  let castSeed := seedLevel (D := D) (A := B.Bin) level
  let oldLevel : lev+2*n+1 = d+2*n+2*n := by omega
  have proj (v : s.input.layout.Site) : productProjection (d+2*n+2*n) (pub.oldLift v) =
      levelCast oldLevel ((child v.1).site v.2) := by
    rw [projLevel oldLevel,dense_lift B child s ω sitesMem hold hchart hproject]
  let code := fun a : (Cube D → Deck (lev+1)) × B.Bin => seedCode radius B.chart n (castSeed a)
  let tile := fun a : (Cube D → Deck (lev+1)) × B.Bin => (castSeed a).1
  have site := preFields_reads enum pat s.input s.label s.perm home s.placed pub old physicalSeed
    (candidateIndex B index) field (fun i => sampledChoice index (ω i)) (fun i j => deckCast level ((ω i).2.2 j))
    code tile raw (by change 0 < d+2*n+2*n; omega)
    (fun v => levelCast oldLevel ((child v.1).site v.2)) valid proj payload
    (fun v => by rw [owner]; exact congrArg (publicMoveCode radius B.chart n) (index.apply_symm_apply _))
    (fun v i => by rw [owner]; exact deckCast_rep level ((ω v.1).2.2 i))
    (fun a => congrArg (Fintype.equivFin _) (seedLevel_bin level a))
    (fun a i => (seedLevel_tile level a i).trans (deckCast_rep level (a.1 i)))
  have eq : preFields enum pat (candidateIndex B index) field physicalSeed code tile x =
      preFields enum pat (candidateIndex B index) field seed (seedCode radius B.chart n) Prod.fst x := by
    funext j
    rcases j with ⟨a,b|b⟩ | ⟨a,b|⟨c,b⟩⟩ | ⟨i,j⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · change seedBits enum pat physicalSeed code tile i j = seedBits enum pat seed (seedCode radius B.chart n) Prod.fst i j
      have selected : castSeed (physicalSeed.symm i) = seed.symm i := castSeed.apply_symm_apply _
      rcases j with b | ⟨i,j⟩
      · change decide (b=seedCode radius B.chart n (castSeed (physicalSeed.symm _))) = _
        rw [selected]; rfl
      · change deckWires _ ((castSeed (physicalSeed.symm _)).1 (enum i)) j = _
        rw [selected]; rfl
  exact eq ▸ site

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
