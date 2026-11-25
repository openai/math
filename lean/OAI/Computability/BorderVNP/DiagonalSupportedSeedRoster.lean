import OAI.Computability.BorderVNP.PackedRetainedReportUse
import OAI.Computability.BorderVNP.CubePhysicalGridReportSlots
import OAI.Computability.BorderVNP.DiagonalTallyReportChoices
import OAI.Computability.BorderVNP.DiagonalCanonicalReportDirectory

/-! # Original power positions on an unverified local report tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

/-- Changing the bits of an occurrence preserves both its bundle ordinal
and its position inside that bundle when its occurrence widths agree. -/
def usePositionsOfCounts (xs ys : List ReportBundle) (equal : xs.map ReportBundle.useCount = ys.map ReportBundle.useCount) :
    UsePositions xs ≃ UsePositions ys := by
  let len : xs.length=ys.length := by simpa using congrArg List.length equal
  refine Equiv.sigmaCongr (finCongr len) (fun i => finCongr ?_)
  have atIndex := congrArg (fun us : List ℕ => us[i.val]?) equal
  have left : i.val<(xs.map ReportBundle.useCount).length := by simp
  have right : i.val<(ys.map ReportBundle.useCount).length := by simp [←len]
  rw [List.getElem?_eq_getElem left,List.getElem?_eq_getElem right] at atIndex
  simpa only [List.getElem_map,finCongr_apply_coe] using Option.some.inj atIndex

end DiagonalTallyCellReports

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes BottomReports Cover TeamContraction GridPlacement
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports Inherited
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {N leaves : ℕ} (origin : Fin N ≃ Fin leaves × (Fin q → Deck (depth+2)))
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin s) (edges : (W.routedFine position).Edge ↪ Fin m)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa)
    {copies C T H : ℕ} (slot base : Fin N → ℕ) (bank : Fin N → ℕ → Bool)
    (home : Fin N → Fin C) (owner : Fin C → ℕ) (team : ℕ)
    (teams : Fin leaves × Fin copies ↪ Fin T) (params : GrammarLabel (Fin n × Bool) (Fin g) n ↪ Fin H)
    {l : ReportLayout} (rs : Fin C → ReportCell l)
local notation3 (prettyPrint := false) "source" => W.retainedBundle (copies := copies) position origin code sites edges ports
  channels groups slot base bank
local notation3 (prettyPrint := false) "staticRows" c => (BundleDirectory.sourceRows home (Fin.val c)).map source
local notation3 (prettyPrint := false) "Owned" => {c : Fin C // owner c=team}

/-- Each unary digit charged by this team corresponds to its own hidden
copy, true grammar parameter and binary place. Only the immutable source
roster and owner directory enter the proof. In particular, this works for
all assignments of the report bits, before the global subtotal check. -/
noncomputable def retainedOwnedPowerSlots
    (shape : ∀ c : {c : Fin C // owner c=team},
      (rs c.val).bundles.map ReportBundle.useCount = (staticRows c.val).map ReportBundle.useCount) :
    ((c : {c : Fin C // owner c=team}) × UsePositions (rs c.val).bundles) ↪
      PowerSlot (Fin T) (Fin H) (Nat.clog 2 (r*(2*d.val+1)+1)) := by
  classical
  let pick := (Fintype.equivFin Owned).symm
  let static (c : Fin C) := {rs c with bundles := staticRows c}
  let data := List.ofFn fun i => static (pick i).val
  let loc : Fin data.length ≃ Owned := (finCongr List.length_ofFn).trans pick
  have retained (i : Fin data.length) : data[i].bundles=staticRows (loc i).val := by
    simp [data,static,loc]
    rfl
  let slots := W.ownedPowerEmbedding position origin code sites edges ports (W.retainedReportStart position origin)
    source (fun _ => rfl) home owner team data loc retained (fun _ => rfl) teams params
    (fun c => staticRows c) retained
  exact (Equiv.sigmaCongrRight fun c : Owned => usePositionsOfCounts _ _ (shape c)).toEmbedding.trans slots

/-- Use the single team's stable source directory and its own live report
tape. Each stream offset can be taken directly from its compact scan. -/
noncomputable def localSourcePowerSlots (buffer supply privateWidth : ℕ → ℕ)
    (digits : ℕ → Fin l.gadgets → Fin l.countWidth → Bool) (tape : ℕ → ℕ → Bool) (cursor : ℕ → ℕ) :
    let atCell := ReportDirectory.sourceCell l home source buffer supply privateWidth digits
    ((c : {c : Fin C // owner c=team}) × UsePositions ((atCell c.val.val).withTape
      (tape c.val.val) (cursor c.val.val)).bundles) ↪
      PowerSlot (Fin T) (Fin H) (Nat.clog 2 (r*(2*d.val+1)+1)) := by
  intro atCell
  apply W.retainedOwnedPowerSlots position origin code sites edges ports channels groups slot base bank
    home owner team teams params (fun c => (atCell c.val).withTape (tape c.val) (cursor c.val))
  intro c
  rw [ReportCell.withTape,tapeBundles_useCount]
  rfl

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
