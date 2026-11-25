import OAI.Computability.BorderVNP.PackedSewnGridTerminal
import OAI.Computability.BorderVNP.PackedTerminalStagedHistorySource

/-! # Chronological site readback on the same staged bus as the signed packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Grid

open Crossing Inherited FrozenTape TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork PackedHistoryCircuit.TerminalCells
open scoped Classical
set_option quotPrecheck false
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000

variable {D R r t pins link inner n V groups copies old : ℕ} {E : Type}
    (G : Wiring R r t pins link inner n E) (hV : 0 < V) (count : groups*copies=R+1)
    (N : Network D (Fin groups × Fin V) (fun _ => copies*blockWidth (r*n) V))
    (h : BlockHosts (FineView.layout N (groupedLane G V hV groups copies count))
      (Equiv.refl (PublicPort R r (G.program.length+t) link)) (blockWidth (r*n) V))
    (hg : 0 < blockWidth (r*n) V) (small : blockWidth (r*n) V ≤ link)
local notation "g" => blockWidth (r*n) V
local notation "lane" => groupedLane G V hV groups copies count
local notation "params" => (⟨R,r,G.program.length+t,link,g,V⟩ : FieldExport.Params)
local notation "room" => gridRoom G hV
local notation "out" => FieldExport.finalLayout params h
local notation "rowPort" => (finProdFinEquiv : Fin groups × Fin V ≃ Fin (groups*V)).toEmbedding
local notation "port" => (finProdFinEquiv : FreeBlock R V ≃ Fin ((R+1)*V)).toEmbedding

variable {σ Geo : Type} [Fintype σ] [Fintype Geo] {s C k w : ℕ}
    (F : Fields s old (groups*V) C w k w σ) (name : ℕ → ℕ → ℕ) (present : Fin old → σ)
    (S : Format) (siteID : N.Site ↪ Fin s) (oldEdge : N.Edge ↪ Fin old)
    {a : ℕ} (oldPort : (Fin groups × Fin V) ↪ Fin a) (progs : Site.Programs N)
local notation "edge" => FieldExport.mergedEdges params (⟨hg,small,room⟩ : (params).Valid) oldEdge
local notation "B" => FieldExport.fields F params name
local notation "raw" => physicalOperands G hV count hg small F name present
local notation "key" => (siteID.trans F.sites).trans Fin.valEmbedding
local notation "restored" => sewnPrograms N lane h.bundle (fun _ : FreeBlock R V => g) (freeLane hg room)
    h.groupOwner (h.groupAligned hg room) oldEdge oldPort edge port progs

/-- The final signed emitter reads its genuine post-sewing chronological tape on
the bus with the new per-site extents. The public fragment compiler still reads
the old geometry columns and their real occupation bits on this bus. -/
theorem staged_terminal_joint_image {Γ : Type} [Fintype Γ] (src : Frame Γ (σ ⊕ Bool)) (input : Γ → Bool) (y : S.Output Geo s w w → Bool)
    (zero : src.eval input (.inr false)=false) (capacity : groups*V=a) (same : ∀ p, (finProdFinEquiv p).val=(oldPort p).val)
    (previous : Views.EndpointData N F siteID oldEdge rowPort (src.eval input ∘ Sum.inl))
    (post : Views.EndpointData out B siteID edge port (src.eval input))
    (occupied : ∀ i, src.eval input (.inl (present i)) = true ↔ i ∈ Set.range oldEdge)
    (history : S.schema.Image (fun z => y (.inr z)) key (fun v => (progs v).program))
    (widths : ∀ v b, value (fun j => y (.inl (.inr (siteID v,b,j)))) =
      if b then (progs v).program.size else (progs v).program.work)
    (fit : ∀ v, (progs v).program.size + incoming out v < 2^w) (one : 1 < 2^w) :
    (S.schema.append (Sewn.schema (2*old+6*(R+1)*V) w)).Image
      ((stagedHistory (Sewn.terminalHistory S F.sites raw)).eval (Sum.elim ((stagedSource B src).eval input) y)) key (fun v => ((restored) v).program) := by
  rw [stagedHistory_eval (Sewn.terminalHistory S F.sites raw) B src input y]
  exact terminal_joint_image G hV count N h hg small F name present S siteID oldEdge oldPort progs
    (src.eval input) y zero capacity same previous post occupied history widths fit one

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
