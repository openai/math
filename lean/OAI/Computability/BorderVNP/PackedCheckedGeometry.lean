import OAI.Computability.BorderVNP.PackedRoundSource
import OAI.Computability.BorderVNP.ShortenPublicRelativeCharged

/-! # One public profile round, through the physically sewn successor

The placement bank and the sparse cable fields share the previous public gates. On every
valid histogram word the output is the complete charged site/cable table of its physical
summand, with the old pointers, new bank sites, actual widths and frozen mask available
for the next stage.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DirectoryCircuit

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Shortening.PublicEndpoints.Successor Shortening.PublicRelative Shortening.PublicSegments
open VPVNP.VerifierNetwork ParseBatchSort BankCircuit Epoch Catalog Cover Cover.AddressCircuit
open scoped Classical

/-- Share a checked cable/record computation across the physical successor and the final flag. -/
noncomputable def physicalPass {σ Geo Fields Out : Type*} [Fintype σ] [Fintype Geo] [Fintype Fields] [Fintype Out]
    (geo : Frame σ Geo) (fields : Frame σ (Fields ⊕ Unit)) (succ : Frame (Geo ⊕ Fields) Out) :
    Frame σ (Out ⊕ Unit) :=
  let raw := parallelFrame geo fields
  let next := succ.subst (Frame.initial (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl) :
    Geo ⊕ Fields → Geo ⊕ (Fields ⊕ Unit)))
  (parallelFrame next (Frame.initial (Sum.inr ∘ Sum.inr))).subst raw

private theorem pass_state {σ Geo Fields Out : Type*} [Fintype σ] [Fintype Geo] [Fintype Fields] [Fintype Out]
    (geo : Frame σ Geo) (fields : Frame σ (Fields ⊕ Unit)) (succ : Frame (Geo ⊕ Fields) Out) (x : σ → Bool) :
    (physicalPass geo fields succ).eval x ∘ Sum.inl =
      succ.eval (Sum.elim (geo.eval x) (fields.eval x ∘ Sum.inl)) := by
  funext i
  simp only [physicalPass,Function.comp_apply,Frame.subst_eval,parallelFrame_eval_inl]
  congr 1
  funext t
  cases t <;> simp

private theorem pass_guard {σ Geo Fields Out : Type*} [Fintype σ] [Fintype Geo] [Fintype Fields] [Fintype Out]
    (geo : Frame σ Geo) (fields : Frame σ (Fields ⊕ Unit)) (succ : Frame (Geo ⊕ Fields) Out) (x : σ → Bool) :
    (physicalPass geo fields succ).eval x (.inr ()) = fields.eval x (.inr ()) := by simp [physicalPass]

private theorem pass_size {σ Geo Fields Out : Type*} [Fintype σ] [Fintype Geo] [Fintype Fields] [Fintype Out]
    (geo : Frame σ Geo) (fields : Frame σ (Fields ⊕ Unit)) (succ : Frame (Geo ⊕ Fields) Out) :
    (physicalPass geo fields succ).size = geo.size + fields.size + succ.size := by simp [physicalPass]

variable {D m q : ℕ} [NeZero D] {K : Type*} [Field K]
variable (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D) (e : PaidIdentity K D m)
variable (S : Finset (HyperbolicHost (Cube D)))

set_option maxHeartbeats 1800000 in
/-- The concrete public stage is chosen before the old layout, profile and placement. A true
guard decodes precisely the complete attained histogram. The other output pins are the actual
next geometric table in the factor and bin order expected by the next reconstruction. -/
theorem checked_geometry_frames (hm : 0 < m) :
    ∃ C E C' E' G H : ℕ, ∀ {A : Type} [Fintype A] {P : Type*} {bits : P → ℕ} (d : ℕ), 1 ≤ d → ∀ (copies nSites M nSeeds k w : ℕ)
      {σ : Type*} [Fintype σ] (p : PublicPopulation.Pins (Fin M) σ k w) (col : Columns σ M D w)
      (code : A ↪ Fin (2^k)) (seed : A ≃ Fin nSeeds) (perm : Fin D → Equiv.Perm A)
      (guess : A → Fin e.count → Fin w → σ) (home : Fin nSites → Fin copies)
      (geo : Frame σ (BatchPorts q pat S d copies nSites nSeeds)),
      nSeeds ≤ 2^w → siteCapacity e nSites nSeeds ≤ 2^w → edgeCapacity e M nSeeds ≤ 2^w →
      let B := ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)
      ∃ f : Frame σ ((Fin (edgeCapacity e M nSeeds) ⊕ Raw B (siteCapacity e nSites nSeeds)
          (edgeCapacity e M nSeeds) w w) ⊕ Unit),
        f.size ≤ geo.size + roundSourceCost (Fintype.card A) D M k w C E C' E' e.count
          (PublicPopulation.offsets p).size (PublicPopulation.frame p code).size +
          ((1+siteCapacity e nSites nSeeds)*G*(d+1)^H + (cost e M nSeeds w + 3*edgeCapacity e M nSeeds)) ∧
        ∀ (pack : Pack D P bits K) (bin : pack.layout.Edge → Option A) (positive : pack.layout.Edge → Bool)
          (oldSite : pack.layout.Site ↪ Fin nSites) (slot : pack.layout.Edge ↪ Fin M) (x : σ → Bool)
          (dummy : Fin (edgeCapacity e M nSeeds) → SiteShape e (densePack pack slot) A),
          Ready e p col code seed pack bin positive oldSite slot dummy x →
          let N := densePack pack slot
          let label := CutCircuit.denseBin pack.layout slot bin
          let rows := CutCircuit.denseRows pack.layout slot
          let pos := positive ∘ (Names.denseSlot pack.layout slot).symm
          let j := blocks N.layout label perm m
          let words := fun a t i => x (guess a t i)
          (f.eval x (.inr ()) = true ↔ Accepted e j words) ∧
          ∀ (lev : ℕ) (hl : lev+1 = d+2*pat.depth)
            (g : Placement (m := m) N label perm (Cube D) (SurfaceHost (Cube D) (lev+1)))
            (placement : PublicPlacement pat S N label perm lev g),
            PlacementReads N label perm enum pat S home g placement oldSite seed.toEmbedding (geo.eval x) →
            ∀ (first : Fin D × Bool) (hist : Counts e N label perm),
            (∀ a t, (hist a).val t = value (words a t)) →
            SegmentReady (pat.nextSites e S) (output e N label perm pos first hist).layout
              (siteRows e N oldSite seed.toEmbedding) (outputRows e N label perm pos first hist rows seed.toEmbedding)
              dummy (g.postSites N label perm e pos hist) (segmentField enum (pat.nextSites e S) hl)
              (postMask N label perm e pos hist) ((f.eval x ∘ Sum.inl) ∘ Sum.inr) ∧
            ∀ i, (f.eval x ∘ Sum.inl) (.inl i) = true ↔
              i ∈ Set.range (outputRows e N label perm pos first hist rows seed.toEmbedding) := by
  obtain ⟨C,E,C',E',prepare⟩ := checked_fields e hm
  obtain ⟨G,H,placed⟩ := uniformOccupiedGeometry_frames enum pat e S
  refine ⟨C,E,C',E',G,H,?_⟩
  intro A _ P bits d hd copies nSites M nSeeds k w σ _ p col code seed perm guess home geo hn hs hc B
  obtain ⟨fields,hf,ef⟩ := prepare nSites M nSeeds k w p col code seed perm guess hn
  obtain ⟨sites,realize,_,hr,er⟩ := placed (A := A) (P := P) (bits := bits) d hd copies nSites M nSeeds w home seed hs hc
  refine ⟨physicalPass geo fields realize,?_,?_⟩
  · rw [pass_size]
    exact Nat.add_le_add (Nat.add_le_add_left hf _) hr
  · intro pack bin positive oldSite slot x dummy ready N label rows pos j words
    obtain ⟨hvalid,hfields⟩ := ef pack bin positive oldSite slot x dummy ready
    constructor
    · rw [pass_guard]
      exact hvalid
    · intro lev hl g pl hgeo first hist hh
      rw [pass_state]
      exact er N label perm lev hl g pl oldSite rows dummy (geo.eval x) hgeo pos first hist
        (fields.eval x ∘ Sum.inl) (hfields first hist hh (sites.eval (geo.eval x)))

end Packing.DirectoryCircuit

end BorderVNP
end Computability
end OAI
