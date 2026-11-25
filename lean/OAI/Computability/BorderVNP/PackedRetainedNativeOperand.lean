import OAI.Computability.BorderVNP.PackedBottomRetainedReports
import OAI.Computability.BorderVNP.PackedGridSeedNativeNames
import OAI.Computability.BorderVNP.CubePhysicalGridReportSlots

/-! # The selected power bit of a true native report occurrence

A physical report ordinal retains the original source site and copy through
the stable cell/bundle enumeration. Its value comes from the actual selected
wire of the surviving prewired term.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open Packing.BundleDirectory
open scoped Classical

private theorem uses_congr {a b : ReportBundle} (eq : a = b) (r : Fin a.positions.length) (i : Fin a.header.copies) :
    a.uses (finProdFinEquiv (r,i)) = b.uses (finProdFinEquiv
      (Fin.cast (congrArg (fun z : ReportBundle => z.positions.length) eq) r,
        Fin.cast (congrArg (fun z : ReportBundle => z.header.copies) eq) i)) := by subst b; rfl

/-- Stable grouping carries the actual stored use bit through the same
source and clone equivalence that decodes its immutable parameter fields. -/
theorem ownedUse_bit {l : ReportLayout} {N C copies : ℕ} {Team Slots : Type*} (cs : List (ReportCell l))
    (owner : Fin N → Fin C) (team : Fin C → Team) (t : Team) (cells : Fin cs.length ≃ {c : Fin C // team c = t})
    (bundle : Fin N → ReportBundle) (grouped : ∀ i : Fin cs.length, cs[i].bundles =
      (sourceRows owner (cells i).val.val).map bundle) (slotRow : Slots → Fin N)
    (clone : ∀ j,(bundle j).header.copies = copies)
    (mark : ∀ j, Fin (bundle j).positions.length ≃ {v : Slots // slotRow v = j})
    (value : Fin copies → Slots → Bool)
    (source : ∀ j r (i : Fin (bundle j).header.copies), (bundle j).uses (finProdFinEquiv (r,i)) =
      value (i.cast (clone j)) (mark j r).val) (u : UseOccurrence cs) :
    let a := ownedUseEquiv cs owner team t cells bundle grouped slotRow clone mark u
    cs[u.1].bundles[u.2.1].uses u.2.2 = value a.1 a.2.val := by
  let b := cs[u.1].bundles[u.2.1]
  let j := (ownedBundleEquiv cs owner team t cells bundle grouped ⟨u.1,u.2.1⟩).val
  have hb : b = bundle j := ownedBundleEquiv_read cs owner team t cells bundle grouped ⟨u.1,u.2.1⟩
  let rc : Fin b.positions.length × Fin b.header.copies := finProdFinEquiv.symm u.2.2
  let rank := rc.1.cast (congrArg (fun z : ReportBundle => z.positions.length) hb)
  let copy := rc.2.cast (congrArg (fun z : ReportBundle => z.header.copies) hb)
  have read : b.uses u.2.2 = b.uses (finProdFinEquiv (rc.1,rc.2)) :=
    congrArg b.uses (finProdFinEquiv.apply_symm_apply u.2.2).symm
  apply read.trans ((uses_congr hb rc.1 rc.2).trans (source j rank copy))

end DiagonalTallyCellReports

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes BottomReports Cover TeamContraction GridPlacement
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin s) (edges : (W.routedFine position).Edge ↪ Fin m)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa)

/-- Equality on the physical deck cells used to read the original hidden assignment. -/
noncomputable local instance selectedDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

local notation "pack₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "rules₀" => W.routedRules position (sidecarReport code)

/-- For a surviving prewired term, its actual source-bit report reads exactly
the corresponding formal power slot at this fine vertex's routed owner. -/
theorem trueReport_selected {Gadget : Type} (z : W.Hidden position) (j : WeightSites n g r d)
    (c : Fin q → Deck (depth+2)) (here : cell position W.route (W.routedPowerSite position j) = c)
    (a x) (alive : W.seedTags (Gadget := Gadget) position z c a x ≠ 0) :
    trueReports rules₀ (cell position W.route) position z pack₀ c a x (sidecarReport code j) =
      (W.seedWords (Gadget := Gadget) position z).selected c a x ((),j) := by
  subst c
  apply W.seed_report position (sidecarReport code) z j _ a x alive
  have h := (W.seed_alive_trueReports (Gadget := Gadget) position (sidecarReport code) (sidecarReport_injective code)
    z _ a x).mp alive
  exact h.2 ⟨W.routedPowerSite position j,rfl⟩

variable (c : Fin q → Deck (depth+2)) (slot base copies : ℕ)
local notation "h₀" => W.seedUseHeader position c slot base copies
local notation "b₀" => W.seedUseBundle position code sites edges ports channels groups c slot base copies
local notation "orig₀" => 3*seedSiteCapacity n r q depth+Inherited.incoming (W.seedGrouped position) c

set_option maxHeartbeats 1000000 in
/-- A real sidecar row and physical clone give the actual selected bit of
the named original power slot, on every surviving grid term. -/
theorem seedUseBundle_selected {Gadget : Type} (z : W.Hidden position) (a x) (bank : ℕ → Bool)
    (i : Fin copies) (r : Fin (W.seedPositions position code sites edges ports c).length)
    (aligned : ∀ k,bank (base+i.val*(h₀).stride+k.val) = physicalBits (cell position W.route) position z
      pack₀ edges ports c a x k)
    (alive : W.seedTags (Gadget := Gadget) position z c a x ≠ 0) :
    let j := W.sidecarEquiv position code sites edges ports c orig₀ r
    (b₀ bank).uses (finProdFinEquiv (r,i)) = (W.seedWords (Gadget := Gadget) position z).selected c a x ((),j.val) := by
  intro j
  apply (W.seedUseBundle_at position code sites edges ports channels groups c slot base copies z a x bank i r aligned).trans
  exact W.trueReport_selected position code z j.val c j.property a x alive

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
