import OAI.Computability.BorderVNP.PackedCheckedGeometry
import OAI.Computability.BorderVNP.PackedHistoryDenseReady

/-! # Reconstructing the actual sorted physical successor and its saved state

The compiled pass is chosen at the public capacities before the input packs,
moved cable labels, placement, or histogram. Its single flag tests the actual
count tuple. For that tuple its output is a ready occupied segment table of
the physically produced and densely saved successor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Cover.AddressCircuit Crossing Epoch Packing Shortening Catalog StaticRows CombiningStep
open BankCircuit PublicRelative PublicSegments VPVNP.VerifierNetwork ParseBatchSort DirectoryCircuit
open scoped Classical BorderVNP.Epoch.Cube

variable {D m q : ℕ} [NeZero D] {K : Type*} [Field K]
    (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost (Cube D)))

set_option maxHeartbeats 2000000 in
/-- One Boolean frame on the genuinely occupied rows, uniformly over the disjoint
child inputs and the selection of each public profile at those inputs. -/
theorem reconstruct_saved (hm : 0 < m) :
    ∃ C E C' E' G H : ℕ, ∀ {B P : Type} [Fintype B] {bits : P → ℕ}
      (d lev prior copies nSites M nSeeds k w : ℕ), 1 ≤ d → (hl : lev+1 = d+2*pat.depth) →
      let Seed := (Cube D → Deck (lev+1)) × B
      ∀ {σ : Type} [Fintype σ] (pins : PublicPopulation.Pins (Fin M) σ k w) (col : Columns σ M D w)
      (code : Seed ↪ Fin (2^k)) (seed : Seed ≃ Fin nSeeds) (perm : Fin D → Equiv.Perm Seed)
      (guess : Seed → Fin e.count → Fin w → σ) (home : Fin nSites → Fin copies)
      (geo : Frame σ (BatchPorts q pat S d copies nSites nSeeds)),
      nSeeds ≤ 2^w → siteCapacity e nSites nSeeds ≤ 2^w → edgeCapacity e M nSeeds ≤ 2^w →
      let Data := ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)
      ∃ f : Frame σ ((Fin (edgeCapacity e M nSeeds) ⊕
          Raw Data (siteCapacity e nSites nSeeds) (edgeCapacity e M nSeeds) w w) ⊕ Unit),
        f.size ≤ geo.size + roundSourceCost (Fintype.card Seed) D M k w C E C' E' e.count
          (PublicPopulation.offsets pins).size (PublicPopulation.frame pins code).size +
          ((1+siteCapacity e nSites nSeeds)*G*(d+1)^H +
            (PublicEndpoints.Successor.cost e M nSeeds w + 3*edgeCapacity e M nSeeds)) ∧
      ∀ (child : Fin copies → PlacedPack D P bits K (Cube D) prior)
        (slot : (raw child).layout.Edge ↪ Fin M) (bin : (raw child).layout.Edge → Option Seed)
        (positive : (raw child).layout.Edge → Bool)
        (g : Placement (m := m) (densePack (raw child) slot) (CutCircuit.denseBin (raw child).layout slot bin)
          perm (Cube D) (SurfaceHost (Cube D) (lev+1))),
        let s : Stage m B lev child := ⟨M,slot,bin,perm,positive,g⟩
        ∀ (old : (raw child).layout.Site ↪ Fin nSites)
          (dummy : Fin (edgeCapacity e M nSeeds) → SiteShape e s.input Seed) (x : σ → Bool),
          Ready e pins col code seed (raw child) bin positive old slot dummy x →
          (f.eval x (.inr ()) = true ↔ Accepted e s.matched (fun a t l => x (guess a t l))) ∧
          ∀ (p : PublicPlacement pat S s.input s.label s.perm lev s.placed),
            PlacementReads s.input s.label s.perm enum pat S home s.placed p old seed.toEmbedding (geo.eval x) →
            ∀ (hist : s.Index e), (∀ a t, (hist a).val t = value (fun j => x (guess a t j))) →
              (s.directory e old seed.toEmbedding dummy hist).dense.Reads (pat.nextSites e S)
                (segmentField enum (pat.nextSites e S) hl) (f.eval x ∘ Sum.inl) := by
  obtain ⟨C,E,C',E',G,H,make⟩ := checked_geometry_frames enum pat e S hm
  refine ⟨C,E,C',E',G,H,?_⟩
  intro B P _ bits d lev prior copies nSites M nSeeds k w hd hl Seed σ _ pins col code seed perm guess home geo hn hs hc Data
  obtain ⟨f,hf,check⟩ := make (A := Seed) (P := Fin copies × P) (bits := fun i => bits i.2) d hd
    copies nSites M nSeeds k w pins col code seed perm guess home geo hn hs hc
  refine ⟨f,hf,?_⟩
  intro child slot bin positive g s old dummy x hx
  obtain ⟨flag,next⟩ := check (raw child) bin positive old slot x dummy hx
  refine ⟨flag,?_⟩
  intro pub reads hist histValue
  have h := next lev hl g pub reads (0,false) hist histValue
  exact Directory.reads_dense _ _ _ ⟨h.1,h.2⟩

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
