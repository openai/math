import OAI.Computability.BorderVNP.CellPacketGeometrySignedMetadata
import OAI.Computability.BorderVNP.CellPacketGeometryOriginalDelivery

/-! # Published signed pointers and cell-local received source metadata

The original payload appears at its emitted pointer in the particular receiving
cell identified by the actual original roster. Between delivery and the typed
task builder only the addressed header and used body of a selected original
need survive, together with the three public source intervals.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open Crossing Packing Packing.Inherited FrozenTape CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellAddressCircuit SiteWords LiveWords ParseBatchSort RoutingISA RoutingISA.CellPacket VPVNP.BurstRAM

section Signed

variable {a m n C d k w entries g digits s p q dest H : ℕ} {σ I Orig : Type} [Fintype σ]
variable (F : Fields a m n C d k w σ) (boxes : Fin a → List (Source.Box Orig)) (entry : Fin entries → Fin a)
variable (arena stride gap desc : ℕ) (x : σ → Bool)
variable (T : Template (FinalReports.Spare.Field C g digits (Fin entries)) I (Fin entries) s (C+1))
variable (fields : Fin s → I → ℕ) (G : SiteWords.Directory (Fin s) (Fin entries) (C+1)) (mem : ℕ → ℕ)

local notation3 "signedArgs" => fun e => value (fun b => (SignedFields.frame F boxes entry arena stride gap desc g digits).eval x (e,b))
local notation3 "emittedSlot" => fun j : Fin entries => (signedArgs) (.inr j)
local notation3 "ptr" => fun j : Fin entries => (Sum.inl (Sum.inr j) : T.Fields)

/-- Every real cell's preserved public intervals have descriptors addressed
by the signed circuit's original pointer fields. The section bounds come from
the actual published marker columns. -/
theorem Published.signedCells (h : Published G p q dest H ptr (T.arguments signedArgs fields) mem) (fs : Fin entries → List Factor) :
    ∃ hf : (C+1)+G.words.length+(C+1)≤2^p,
    ∃ hs : (C+1)+(CellPacketGeometry.Schema.coords (G.referenceRows ptr).length).length+(C+1)≤2^q,
    ∀ c : Fin C, ∀ ext scratch burst external,
      let words := sectionRange mem dest (Markers.start hf c.castSucc) (Markers.stop hf c.castSucc)
      let table := sectionRange mem (descriptorBank dest p) (Markers.start hs c.castSucc) (Markers.stop hs c.castSucc)
      let placed := G.placed c.castSucc H emittedSlot fs words.1 table.1 ext scratch burst external
      let geom := words.1+((Supplement.prefixParts placed).flatMap Part.publicBuffer).length
      CellMemory placed geom (descriptorBank dest p+mem (descriptorBank dest p+(2^q+(Markers.stop hs c.castSucc).val))) mem := by
  obtain ⟨hf,hs,all⟩ := h.cells emittedSlot fs (fun _ => rfl)
  exact ⟨hf,hs,fun c => all c.castSucc⟩

end Signed

private theorem prefix_original {O : Type} (p : Placed O) (j : O) :
    Part.original j∈Supplement.prefixParts p ↔ j∈p.boxes.filterMap Sum.getRight? := by
  simp only [Supplement.prefixParts,List.mem_cons,reduceCtorEq,false_or,List.mem_map,List.mem_filterMap]
  constructor
  · rintro ⟨b,hb,h⟩
    rcases b with fs|i
    · exact nomatch h
    · exact ⟨.inr i,hb,congrArg some (Part.original.inj h)⟩
  · rintro ⟨b,hb,h⟩
    rcases b with fs|i
    · exact nomatch h
    · exact ⟨.inr i,hb,congrArg Part.original (Option.some.inj h)⟩

section Received

variable {a C cap d t J w description : ℕ} {R B U V E : Type}
variable (S : FrozenTape.Schema R B) (L : FrozenTape.Schema U V) (entry : Fin J ↪ Fin a) (known : Fin a → List (List Factor))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
variable (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)

local notation3 "G₀" => directory S L (originalBoxes entry known) sh lh priv rep args x y cells off box

/-- An original present in this real cell's source prefix is owned by this
same cell according to the retained physical entry map. -/
theorem originalPrefix_receiver (c : Fin C) (p : Placed (Fin J)) (hb : p.boxes=(G₀).cellBoxes c.castSucc)
    (j : Fin J) (selected : Part.original j∈Supplement.prefixParts p) : cells (entry j)=c := by
  apply (originalDelivery_mem S L entry known sh lh priv rep args x y cells off box c j).mp
  rw [←hb]
  exact (prefix_original p j).mp selected

/-- Transport the real receiving cell's literal to the memory checkpoint read
by the task builder. Only meaningful bytes of selected descriptions are read. -/
theorem delivered_at_checkpoint (c : Fin C) (p : Placed (Fin J)) (hb : p.boxes=(G₀).cellBoxes c.castSucc)
    (received : Fin C → Memory w) (m : Memory w)
    (receipt : ∀ j, Delivered (description:=description) (readings (received (cells (entry j)))) (p.slot j) p.headerWidth (p.factors j))
    (kept : ∀ j, Part.original j∈Supplement.prefixParts p → ∀ b : Fin description, b.val<(siteData p.headerWidth (p.factors j)).length →
      readings m (p.slot j+b.val)=readings (received c) (p.slot j+b.val))
    (j : Fin J) (selected : Part.original j∈Supplement.prefixParts p) :
    Delivered (description:=description) (readings m) (p.slot j) p.headerWidth (p.factors j) := by
  have h := receipt j
  rw [originalPrefix_receiver S L entry known sh lh priv rep args x y cells off box c p hb j selected] at h
  exact fun b used => (kept j selected b used).trans (h b used)

/-- Published geometry and the genuine per-owner received bytes provide the
three public source sections and private opaque chunks read from the same
post-builder memory. All preservation is restricted to those sections. -/
theorem CellMemory.metadata_received (c : Fin C) (owned : Supplement.Batch.Owned (Fin J))
    (hb : owned.placed.boxes=(G₀).cellBoxes c.castSucc) {exclusive : ℕ} {origin : ℕ → ℕ}
    (pub : CellMemory owned.placed owned.geometry exclusive origin) (received : Fin C → Memory w) (m : Memory w)
    (receipt : ∀ j, Delivered (description:=description) (readings (received (cells (entry j))))
      (owned.placed.slot j) owned.placed.headerWidth (owned.placed.factors j))
    (kept : ∀ j, Part.original j∈Supplement.prefixParts owned.placed → ∀ b : Fin description,
      b.val<(siteData owned.placed.headerWidth (owned.placed.factors j)).length →
      readings m (owned.placed.slot j+b.val)=readings (received c) (owned.placed.slot j+b.val))
    (descKept : ∀ i : Fin (descriptors (Supplement.prefixChunks owned.placed)).length,
      readings m (owned.placed.descriptorBase+i.val)=origin (owned.placed.descriptorBase+i.val))
    (pubKept : ∀ i : Fin ((Supplement.prefixParts owned.placed).flatMap Part.publicBuffer).length,
      readings m (owned.placed.publicBase+i.val)=origin (owned.placed.publicBase+i.val))
    (geomKept : ∀ i : Fin (fieldList record owned.placed.rows++fieldList vector owned.placed.reports).length,
      readings m (owned.geometry+i.val)=origin (owned.geometry+i.val))
    (room : ∀ j, owned.placed.headerWidth+(boxBody (owned.placed.factors j)).length≤description)
    (fits : ∀ j, (boxBody (owned.placed.factors j)).length<2^owned.placed.headerWidth)
    (extra : WordsAt (readings m) owned.layout.supplement (owned.extra.flatMap record)) :
    Supplement.Batch.Original owned.metadata owned.layout owned.geometry owned.extra m :=
  pub.metadata owned m descKept pubKept geomKept
    (delivered_at_checkpoint S L entry known sh lh priv rep args x y cells off box c owned.placed hb received m receipt kept)
    room fits extra

end Received
end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
