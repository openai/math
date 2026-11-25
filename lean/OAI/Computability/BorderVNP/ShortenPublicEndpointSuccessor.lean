import OAI.Computability.BorderVNP.ShortenPublicEndpointMerge
import OAI.Computability.BorderVNP.ShortenStaticOldRows

/-!
# Public cable and site table for the next shortening epoch

One circuit consumes the preceding cut descriptors, site payloads and histogram
counts. Its rows describe the actual sewn layout, including the unused slots, on
every branch. A single copy of the frame producing these inputs suffices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicEndpoints.Successor

open Crossing SeedIntervals CombiningStep StaticRows ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
variable {nSites nEdges nSeeds w : ℕ} (oldSite : p.layout.Site ↪ Fin nSites)
variable (old : p.layout.Edge ↪ Fin nEdges) (seed : A ≃ Fin nSeeds)
variable (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A)
variable (first : Fin D × Bool) (q : Counts e p bin perm) {B : Type*}

/-- Input to the successor serializer after interval cuts and the shared histogram computation. -/
abbrev Source (B A : Type*) (nSites nEdges nSeeds w : ℕ) :=
  (Fin (siteCapacity e nSites nSeeds) × B) ⊕ (Serializer.Row nEdges D × Serializer.DirectoryInput w) ⊕
    (A × Option (Fin e.count) × Fin w)

/-- The data consumed by the cable and bank serializers are the actual current-round outputs. -/
structure SourceData (x : Source e B A nSites nEdges nSeeds w → Bool) : Prop where
  /-- Cut, inverse-seed and old cable records at every physical candidate, including padding. -/
  directory : ∀ r, Serializer.DirectoryRepresents e p bin perm positive oldSite old seed.toEmbedding dummy r
    (fun t => x (.inr (.inl (r,.inl t))))
    (fun t => value (fun j => x (.inr (.inl (r,.inr (t,j)))) ))
  /-- Matched block count and multiplicities of every term in the branch histogram. -/
  histogram : ∀ a (i : Option (Fin e.count)), value (fun j => x (.inr (.inr (a,i,j)))) =
    i.elim (blocks p.layout bin perm m a) (q a).val
  /-- All emitted bank cable widths fit in the width field. -/
  bankWidths : ∀ a u, Packing.BankCircuit.physical e p bin perm positive first q oldSite old seed.toEmbedding a u .width < 2^w

/-- Complete correspondence between the compiled successor table and the sewn pack. -/
structure Result (x : Source e B A nSites nEdges nSeeds w → Bool)
    (y : Next B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w → Bool) : Prop where
  /-- Old and new site records have their prescribed public data. -/
  sites : ∀ z, y (.inl (.inl z)) = x (.inl z)
  /-- Endpoint words and widths are correct at every cable number, including holes. -/
  rows : PublicEndpoints.Represents (output e p bin perm positive first q).layout (siteRows e p oldSite seed.toEmbedding)
    (outputRows e p bin perm positive first q old seed.toEmbedding) dummy (y ∘ Sum.inl)
  /-- The enable bit agrees with physical cable presence independently of its width. -/
  occupied : ∀ i, y (.inr i) = true ↔ i ∈ Set.range (outputRows e p bin perm positive first q old seed.toEmbedding)

private theorem bank_padded (a : A) (u : TemplateEdge e) (col : Serializer.Column) :
    Packing.BankCircuit.physical e p bin perm positive first q oldSite old seed.toEmbedding a u (bankColumn col) =
      Serializer.fieldAt (Packing.Names.layout (output e p bin perm positive first q).layout
        (outputRows e p bin perm positive first q old seed.toEmbedding) dummy)
        (siteRows e p oldSite seed.toEmbedding) (Packing.Names.rowSlot (candidateEquiv e nEdges seed (.inr (a,u)))) col := by
  rw [candidateEquiv_bank e p bin perm old seed]
  let L := (output e p bin perm positive first q).layout
  let names := outputRows e p bin perm positive first q old seed.toEmbedding
  let z : L.Edge := .inr (.inr ⟨a,u⟩)
  cases col
  · exact congrArg (fun v => (siteRows e p oldSite seed.toEmbedding v).val) (Packing.Names.src_slot L names dummy z).symm
  · exact congrArg (fun v => (siteRows e p oldSite seed.toEmbedding v).val) (Packing.Names.dst_slot L names dummy z).symm
  · exact (Packing.Names.width_slot L names dummy z).symm

/-- Gate budget of the combined serializer, after sharing its incoming table. -/
def cost (nEdges nSeeds w : ℕ) : ℕ :=
  3 + nEdges*(2*D+1)*3 * (2*StaticTerminalCircuit.nodeBudget e * (100*(w+1)^2) + 64*(1+3*w)) +
    nSeeds * (4 * (∑ u : TemplateEdge e, Packing.BankCircuit.nodeBudget e u) * (100*(w+1)^2))

set_option maxHeartbeats 2000000 in
/-- A fixed Boolean frame produces the next table for every choice of the old pack, bins and
histogram, at a cost linear in the number of candidate rows and quadratic in word length. -/
theorem exists_frame (B : Type*) [Fintype B] (nSites nEdges w : ℕ) (seed : A ≃ Fin nSeeds)
    (siteFits : siteCapacity e nSites nSeeds ≤ 2^w) (edgeFits : edgeCapacity e nEdges nSeeds ≤ 2^w) :
    ∃ f : Frame (Source e B A nSites nEdges nSeeds w)
        (Next B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w),
      f.size ≤ cost e nEdges nSeeds w ∧
      ∀ {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option A)
        (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
        (oldSite : p.layout.Site ↪ Fin nSites) (old : p.layout.Edge ↪ Fin nEdges)
        (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A)
        (first : Fin D × Bool) (q : Counts e p bin perm) (x : Source e B A nSites nEdges nSeeds w → Bool),
        SourceData e p bin perm positive oldSite old seed dummy first q x →
          Result e p bin perm positive oldSite old seed dummy first q x (f.eval x) := by
  let S := Source e B A nSites nEdges nSeeds w
  let sites : Frame S (Fin (siteCapacity e nSites nSeeds) × B) := Frame.initial Sum.inl
  let dir : Frame S (Serializer.Row nEdges D × Serializer.DirectoryInput w) := Frame.initial (Sum.inr ∘ Sum.inl)
  let hist : Frame S (A × Option (Fin e.count) × Fin w) := Frame.initial (Sum.inr ∘ Sum.inr)
  obtain ⟨fo,hfo,eo⟩ := Serializer.exists_physical_oldRows e nSites nEdges w dir
  obtain ⟨fb,hfb,eb⟩ := Packing.BankCircuit.exists_bankFrame e (fun a => (seed a).val) nSites nEdges w hist
  let f := merge e seed sites fo fb
  refine ⟨f,?_,?_⟩
  · have hsize := merge_size e seed sites fo fb
    have ha : Fintype.card A = nSeeds := (Fintype.card_congr seed).trans (Fintype.card_fin _)
    rw [ha] at hfb
    simp only [sites,dir,hist,Frame.initial_size,zero_add] at hsize hfo hfb
    dsimp only [f,cost,sites]
    omega
  intro P bits p bin perm positive oldSite old dummy first q x h
  let L := (output e p bin perm positive first q).layout
  let names := outputRows e p bin perm positive first q old seed.toEmbedding
  let verts := siteRows e p oldSite seed.toEmbedding
  let padded := Packing.Names.layout L names dummy
  have oldVals (r : Serializer.Row nEdges D) := eo p bin perm positive oldSite old seed.toEmbedding dummy x r
    siteFits (by simpa [dir,Function.comp_def] using h.directory r) first q
  have bankVals (a : A) (u : TemplateEdge e) (c : Packing.BankCircuit.Column) :
      value (fun j => fb.eval x (a,u,c,j)) =
        Packing.BankCircuit.physical e p bin perm positive first q oldSite old seed.toEmbedding a u c := by
    let raw (i : Option (Fin e.count)) := value (fun j => hist.eval x (a,i,j))
    have he : raw = fun i => i.elim (blocks p.layout bin perm m a) (q a).val := by
      funext i
      simpa [raw,hist] using h.histogram a i
    have hr : Packing.BankCircuit.read e (fun s => (seed s).val) nSites nEdges a u raw c =
        Packing.BankCircuit.physical e p bin perm positive first q oldSite old seed.toEmbedding a u c := by
      rw [he]
      exact Packing.BankCircuit.read_physical e p bin perm positive first q oldSite old seed.toEmbedding a u c
    have room : Packing.BankCircuit.physical e p bin perm positive first q oldSite old seed.toEmbedding a u c < 2^w := by
      cases c
      · exact (names _).isLt.trans_le edgeFits
      · exact (verts _).isLt.trans_le siteFits
      · exact (verts _).isLt.trans_le siteFits
      · exact h.bankWidths a u
    exact (eb x a u c (hr.trans_lt room)).trans hr
  have fields (i : Fin (edgeCapacity e nEdges nSeeds)) (col : Serializer.Column) :
      value (fun j => f.eval x (.inl (fieldPin i col j))) =
        Serializer.fieldAt padded verts (Packing.Names.rowSlot i) col := by
    obtain ⟨r,rfl⟩ := (candidateEquiv e nEdges seed).surjective i
    rcases r with r | ⟨a,u⟩
    · rw [show f = merge e seed sites fo fb from rfl,merge_field_old,candidateEquiv_old]
      exact (oldVals r).2 col
    · exact (merge_field_bank e seed sites fo fb x a u col).trans
        ((bankVals a u _).trans (bank_padded e p bin perm positive oldSite old seed dummy first q a u col))
  refine ⟨fun z => (merge_site e seed sites fo fb x z.1 z.2).trans (Frame.initial_eval _ _ _),
    ⟨?_,fun i => fields i .width⟩,?_⟩
  · intro i side
    cases side
    · exact fields i .dst
    · exact fields i .src
  · intro i
    obtain ⟨r,rfl⟩ := (candidateEquiv e nEdges seed).surjective i
    rcases r with r | ⟨a,u⟩
    · rw [show f = merge e seed sites fo fb from rfl,merge_present_old,candidateEquiv_old]
      exact (oldVals r).1
    · exact iff_of_true (merge_present_bank e seed sites fo fb x a u)
        ⟨.inr (.inr ⟨a,u⟩), (candidateEquiv_bank e p bin perm old seed a u).symm⟩

end Shortening.PublicEndpoints.Successor

end BorderVNP
end Computability
end OAI
