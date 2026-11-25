import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomParameters
import OAI.Computability.BorderVNP.PackedRetainedReportUse

/-! # Source rows and unary uses in the selected signed report allocation

Original bundle ordinals enumerate a leaf and a seed-grid tile. The one-copy
mark list is the sidecar read from that tile's true compact packet. Repeating
those marks for every genuine original copy counts exactly one occurrence for
each batch, grammar label and exponent place before filtering by final owner.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes BottomReports Cover TeamContraction GridPlacement
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports DiagonalTallyAllocation RoutingISA.SignedTaskArena
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical BigOperators

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    {N leaves copies : ℕ}
    (wits : Fin leaves → WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (origin : Fin N ≃ Fin leaves × (Fin q → Deck (depth+2)))
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (sites : ∀ i, ((wits i).routedFine position).Site ↪ Fin s)
    (edges : ∀ i, ((wits i).routedFine position).Edge ↪ Fin m)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa)
    (slot base : Fin N → ℕ) (bank : Fin N → ℕ → Bool)

local notation "V" => (Fin q → Deck (depth+2))
local notation "marked" => seedSiteCapacity n r q depth
local notation "expBits" => Nat.clog 2 (r*(2*d.val+1)+1)
local notation "Label" => GrammarLabel (Fin n × Bool) (Fin g) n

/-- Each actual source ordinal carries its original leaf's own routed seed
box, opaque factor body, sidecar, repetition and receiving-bank bits. -/
noncomputable abbrev physicalReportRow (j : Fin N) : ReportBundle :=
  let i := (origin j).1
  (wits i).seedUseBundle position code (sites i) (edges i) ports channels groups (origin j).2
    (slot j) (base j) copies (bank j)

local notation "source" => physicalReportRow (copies:=copies) wits position origin code sites edges
  ports channels groups slot base bank

/-- The original bundle count, the one-copy mark bound, and the global
expanded use count hold for independent choices of every leaf witness. -/
theorem physicalReportInventory :
    N = leaves*GridHosts.tileCount q depth ∧ (∀ j, (source j).positions.length ≤ marked) ∧
    (∑ j, (source j).useCount) = leaves*Fintype.card Label*expBits*copies := by
  have count : N=leaves*GridHosts.tileCount q depth := by
    simpa only [Fintype.card_prod,Fintype.card_fin,GridHosts.tileCount] using Fintype.card_congr origin
  refine ⟨count,fun j => (wits (origin j).1).seedPositions_length position code (sites _) (edges _) ports _,?_⟩
  let next (i : Fin leaves) (v : V) := 3*marked + Inherited.incoming ((wits i).seedGrouped position) v
  let uses (z : Fin leaves × V) :=
    ((wits z.1).sidecarPositions position code (sites z.1) (edges z.1) ports z.2 (next z.1 z.2)).length*copies
  change (∑ j, uses (origin j)) = _
  rw [origin.sum_comp uses,Fintype.sum_prod_type]
  exact sidecar_total_witnesses position code ports leaves copies wits sites edges next

variable (arena : RoutingISA.CubeArena.Layout) {H : ℕ}
    (teamNumbers : Fin leaves × Fin copies ↪ Fin arena.teams) (params : GrammarLabel (Fin n × Bool) (Fin g) n ↪ Fin H)
    (gadgets word : ℕ)
local notation "bound" => reportBounds arena (leaves*GridHosts.tileCount q depth) marked H expBits gadgets word

include teamNumbers params in
/-- All source-side premises of the native report allocator hold for the
actual seed rows and the selected physical reservation. In particular every
retained bundle contributes its six fixed supplemental words even if empty. -/
theorem physicalReportRows_room (owner : Fin N → Fin arena.cells) :
    N=(bound).bundles ∧ (∀ j, (source j).positions.length ≤ (bound).marked) ∧
    (∑ j, (source j).useCount) ≤ (bound).uses ∧
    ∀ cell : Fin arena.cells, supplementWords ((BundleDirectory.sourceRows owner cell.val).map source) ≤
      (bound).supplementStride := by
  obtain ⟨count,marks,total⟩ := physicalReportInventory (copies:=copies) wits position origin code sites
    edges ports channels groups slot base bank
  have teams : leaves*copies ≤ arena.teams := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_embedding teamNumbers
  have pars : Fintype.card Label ≤ H := by simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding params
  refine ⟨count,marks,?_,?_⟩
  · rw [total]
    calc
      leaves*Fintype.card Label*expBits*copies = (leaves*copies)*(Fintype.card Label*expBits) := by ring
      _ ≤ arena.teams*(H*expBits) := Nat.mul_le_mul teams (Nat.mul_le_mul_right _ pars)
  · intro cell
    have supp := report_supplement arena N marked H expBits gadgets word owner cell source marks
    change _ ≤ (leaves*GridHosts.tileCount q depth)*(9*marked+6)
    change _ ≤ N*(9*marked+6) at supp
    exact count ▸ supp

include teamNumbers params in
/-- The physical signed layout and retained original row directory supply the
report scanner's complete allocation certificate. The receiving hypothesis
is the actual bank width of each named local cell. -/
theorem physicalReportAllocation (task : Layout) (geometry : task.cube=arena)
    (chosen : task.p.report=bound) (banks : RoutingISA.CellBanks.Layout)
    (bankCells : banks.cells=arena.cells) (bankBase : banks.bankStart=arena.cellBank)
    (bankWidth : banks.stride=arena.cellStride) (frame control header body zeroAddr : ℕ)
    (lower : frame+96 ≤ arena.cellBank) (owner : Fin N → Fin arena.cells)
    (team : Fin arena.cells → ℕ) (current : ℕ)
    (cs : List (ReportCell (reportLayout task.before task.after frame control H header body zeroAddr)))
    (cells : Fin cs.length ≃ {v : Fin arena.cells // team v=current})
    (numbers : ∀ i, cs[i].number=(cells i).val.val)
    (grouped : ∀ i : Fin cs.length, cs[i].bundles=(BundleDirectory.sourceRows owner (cells i).val.val).map source)
    (receive : ∀ c∈cs, c.external=banks.bank c.number ∧ c.supplied+c.tailWidth ≤ banks.stride) :
    ReportAllocation task.before task.after banks (reportLayout task.before task.after frame control H header body zeroAddr)
      cs task.after.reportCursor := by
  obtain ⟨cnt,marks,uses,supp⟩ := physicalReportRows_room wits position origin code sites edges ports
    channels groups slot base bank arena teamNumbers params gadgets word owner
  have cellsEq : task.before.bound.cells=arena.cells := congrArg Bounds.cells chosen
  have before : banks.bankStart+banks.cells*banks.stride ≤ task.before.start := by
    rw [bankBase,bankCells,bankWidth]
    change arena.stop ≤ _
    rw [← geometry]
    apply LE.le.trans _ task.constants_le_before
    unfold RoutingISA.CubeConstants.arenaEnd RoutingISA.CubeConstants.idBase
    omega
  have after : task.before.limit ≤ task.after.start := by
    change _ ≤ task.before.limit+3*task.cube.cells+7*task.cube.cells+
      task.p.scratchStride*task.cube.cells+task.p.burstStride*task.cube.cells
    omega
  apply ReportAllocation.of_sourceRows task.before task.after banks frame control H header body zeroAddr cs
    cellsEq.ge owner team current cells source numbers grouped (bankCells.trans cellsEq.symm) rfl
    (bankBase.symm ▸ lower) before after receive
  · rw [show task.before.bound=bound from chosen]; exact supp
  · rw [show task.after.bound=bound from chosen]; exact cnt.le
  · rw [show task.after.bound=bound from chosen]; exact marks
  · rw [show task.after.bound=bound from chosen]; exact uses

/-- Instantiate the original power-slot injection for the canonical single
seed witness and the actual stable final-owner enumeration. No report bits
are spent a second time when several seeds end in the same final cell. -/
noncomputable def retainedOwnedPowerEmbedding
    (W : WiredWitness G d D q depth order state)
    (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (owner : Fin N → Fin arena.cells) (team : Fin arena.cells → ℕ) (current : ℕ)
    {l : ReportLayout} (cs : List (ReportCell l)) (cells : Fin cs.length ≃ {v : Fin arena.cells // team v=current})
    (ordered : ∀ i : Fin cs.length, cs[i].bundles = (BundleDirectory.sourceRows owner (cells i).val.val).map
      (W.retainedBundle (copies:=copies) position origin code siteID edgeID ports channels groups slot base bank)) :
    ((v : {v : Fin arena.cells // team v=current}) × UsePositions ((BundleDirectory.sourceRows owner v.val.val).map
      (W.retainedBundle (copies:=copies) position origin code siteID edgeID ports channels groups slot base bank))) ↪
      PowerSlot (Fin arena.teams) (Fin H) expBits :=
  W.ownedPowerEmbedding position origin code siteID edgeID ports (W.retainedReportStart position origin)
    (W.retainedBundle (copies:=copies) position origin code siteID edgeID ports channels groups slot base bank)
    (fun _ => rfl) owner team current cs cells ordered (fun _ => rfl) teamNumbers params
    (fun v => (BundleDirectory.sourceRows owner v.val).map
      (W.retainedBundle (copies:=copies) position origin code siteID edgeID ports channels groups slot base bank)) ordered

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
