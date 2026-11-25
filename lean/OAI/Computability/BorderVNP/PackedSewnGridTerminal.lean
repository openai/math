import OAI.Computability.BorderVNP.PackedSewnTerminalHistory
import OAI.Computability.BorderVNP.PackedSewnPhysicalOperands
import OAI.Computability.BorderVNP.PackedHistorySewnTagModels

/-! # The public terminal tape of the genuinely sewn grid

Both physical operand passes, sorting and coalescing, work/extent lookups,
and the saved chronological tape are evaluated on the two actual terminal
banks. The old evaluator may index its grouped ports by an equivalent finite
capacity. Numeric port names determine exactly the same lane order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Grid

open Crossing Inherited FrozenTape TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
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

/-- The physically compiled chronological history on the exact field names and the
actual private old input order, after restoration of all closed, live and padding lanes. -/
theorem terminal_joint_image (x : σ ⊕ Bool → Bool) (y : S.Output Geo s w w → Bool)
    (zero : x (.inr false)=false) (capacity : groups*V=a) (same : ∀ p, (finProdFinEquiv p).val=(oldPort p).val)
    (previous : Views.EndpointData N F siteID oldEdge rowPort (x ∘ Sum.inl))
    (post : Views.EndpointData out B siteID edge port x)
    (occupied : ∀ i, x (.inl (present i)) = true ↔ i ∈ Set.range oldEdge)
    (history : S.schema.Image (fun z => y (.inr z)) key (fun v => (progs v).program))
    (widths : ∀ v b, value (fun j => y (.inl (.inr (siteID v,b,j)))) =
      if b then (progs v).program.size else (progs v).program.work)
    (fit : ∀ v, (progs v).program.size + incoming out v < 2^w) (one : 1 < 2^w) :
    (S.schema.append (Sewn.schema (2*old+6*(R+1)*V) w)).Image
      ((Sewn.terminalHistory S F.sites raw).eval (Sum.elim x y)) key (fun v => ((restored) v).program) := by
  have oldFit (v) : incoming N v < 2^w := by
    have b := fit v
    change (progs v).program.work + (progs v).program.incoming + incoming out v < 2^w at b
    rw [(progs v).size] at b
    omega
  have newFit (v) : incoming out v < 2^w := (Nat.le_add_left _ _).trans_lt (fit v)
  have real := physicalOperands_image G hV count N h hg small oldEdge rowPort F name present siteID x zero
    (fun _ => rfl) previous post occupied oldFit newFit
  let source := sewnRead N lane h.bundle (fun _ : FreeBlock R V => g) (freeLane hg room) h.groupOwner
    (h.groupAligned hg room) oldEdge oldPort edge port
  have castRead (v) := sewnRead_ports N lane h.bundle (fun _ : FreeBlock R V => g) (freeLane hg room) h.groupOwner
    (h.groupAligned hg room) oldEdge rowPort oldPort edge port capacity same v
  let readOld := fun v => source v ∘ Fin.cast (progs v).size
  apply Sewn.terminalHistory_image S F.sites raw siteID (fun v => (progs v).program) (incoming out)
    readOld x y history real.1 _ _ widths fit one
  · intro v
    have cov := (real.2 v).1
    rw [castRead v] at cov
    let actual := Fragment.siteRuns ((F.sites (siteID v)).val) (Fragment.list ((raw).eval x))
    have lift {a b : ℕ} (h : a=b) (f : Fin b → Option (Fin (incoming out v))) (ok : Covers actual f) :
        Covers actual (f ∘ Fin.cast h) := by subst b; exact ok
    exact lift (progs v).size (source v) cov
  · intro v
    rw [(progs v).size]
    exact (real.2 v).2

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
