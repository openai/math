import OAI.Computability.BorderVNP.CubePhysicalOwnedReportSlots
import OAI.Computability.BorderVNP.PackedGridSidecar
import OAI.Computability.BorderVNP.CellTeamReportCharge

/-! # Charging every emitted unary report to its true original signed-grid power slot -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse BottomReports GridBoxes Diagonal.CellEntries GridPlacement Cover TeamContraction TallySidecar
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar DiagonalTallyCellReports
open scoped Classical
set_option maxHeartbeats 1600000

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {N leaves : ℕ} (origin : Fin N ≃ Fin leaves × (Fin q → Deck (depth+2)))

/-- Actual original bundle row containing a one-copy source mark of a specified leaf. -/
noncomputable def weightRow (u : Fin leaves × WeightSites n g r d) : Fin N :=
  origin.symm (u.1,cell position W.route (W.routedPowerSite position u.2))

private theorem weightRow_iff (u : Fin leaves × WeightSites n g r d) (src : Fin N) :
    W.weightRow position origin u = src ↔ u.1 = (origin src).1 ∧
      cell position W.route (W.routedPowerSite position u.2) = (origin src).2 := by
  exact origin.symm_apply_eq.trans Prod.ext_iff

/-- The actual owner-cell subset of the original grid's source marks is precisely the
fiber of the original bundle table at this source ordinal. -/
noncomputable def weightFiber (src : Fin N) :
    W.OwnedSlot position (origin src).2 ≃ {u : Fin leaves × WeightSites n g r d // W.weightRow position origin u = src} where
  toFun j := ⟨((origin src).1,j.val),(W.weightRow_iff position origin _ _).mpr ⟨rfl,j.property⟩⟩
  invFun u := ⟨u.val.2,((W.weightRow_iff position origin _ _).mp u.property).2⟩
  left_inv _ := rfl
  right_inv u := Subtype.ext (Prod.ext (((W.weightRow_iff position origin _ _).mp u.property).1.symm) rfl)

variable (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p) (next : Fin N → ℕ)
    (bundle : Fin N → ReportBundle)
    (sourceRead : ∀ j, (bundle j).positions = W.sidecarPositions position code siteID edgeID portID (origin j).2 (next j))

/-- Read one actual emitted source position and invert its physical one-copy sidecar. -/
noncomputable def reportMark (j : Fin N) :
    Fin (bundle j).positions.length ≃ {u : Fin leaves × WeightSites n g r d // W.weightRow position origin u = j} :=
  ((finCongr (congrArg List.length (sourceRead j))).trans (W.sidecarEquiv position code siteID edgeID portID (origin j).2 (next j))).trans
    (W.weightFiber position origin j)

/-- The one-copy report read from the source ordinal has the actual parameter, place
and relative staging address of the formal grid slot recovered at that ordinal. -/
theorem reportMark_fields (j : Fin N) (i : Fin (bundle j).positions.length) :
    let u := W.reportMark position origin code siteID edgeID portID next bundle sourceRead j i
    let p := (bundle j).positions[i]
    p.parameter = code u.val.2.1 ∧ p.place = u.val.2.2.val ∧ p.stagedReportRel = next j+i.val := by
  let ps := W.sidecarPositions position code siteID edgeID portID (origin j).2 (next j)
  let k := Fin.cast (congrArg List.length (sourceRead j)) i
  have h := W.sidecarEquiv_fields position code siteID edgeID portID (origin j).2 (next j) k
  have atIndex : (bundle j).positions[i] = ps[k] := by
    have eq := congrArg (fun z : List Position => z[i.val]?) (sourceRead j)
    change (bundle j).positions[i.val]? = ps[k.val]? at eq
    rw [List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem k.isLt] at eq
    exact Option.some.inj eq
  change _ = _ ∧ _ = _ ∧ _ = _
  rw [atIndex]
  exact h

variable {C copies T H : ℕ} (owner : Fin N → Fin C) (team : Fin C → ℕ) (current : ℕ)
    {l : ReportLayout} (cs : List (ReportCell l)) (cells : Fin cs.length ≃ {c : Fin C // team c = current})
    (grouped : ∀ i : Fin cs.length, cs[i].bundles = (BundleDirectory.sourceRows owner (cells i).val.val).map bundle)
    (clone : ∀ j, (bundle j).header.copies = copies)

/-- Exact chronological reports of one routed processor correspond to an original copy,
leaf, grammar parameter and exponent bit on its own actual chosen owner row. -/
noncomputable def reportUseEquiv :
    UseOccurrence cs ≃ Fin copies × {v : Fin leaves × WeightSites n g r d // team (owner (W.weightRow position origin v)) = current} :=
  ownedUseEquiv cs owner team current cells bundle grouped (W.weightRow position origin) clone
    (W.reportMark position origin code siteID edgeID portID next bundle sourceRead)

set_option maxHeartbeats 1600000 in
/-- The compact scanner uses the recovered original parameter and exponent place on
this precise clone. The site-local prefix remains part of the physical address. -/
theorem reportUse_fields (u : UseOccurrence cs) :
    let a := W.reportUseEquiv position origin code siteID edgeID portID next bundle sourceRead
      owner team current cs cells grouped clone u
    let p := cs[u.1].bundles[u.2.1].source u.2.2
    p.parameter = code a.2.val.2.1 ∧ p.place = a.2.val.2.2.val := by
  let b := cs[u.1].bundles[u.2.1]
  let j := (ownedBundleEquiv cs owner team current cells bundle grouped ⟨u.1,u.2.1⟩).val
  have hb : b = bundle j := ownedBundleEquiv_read cs owner team current cells bundle grouped ⟨u.1,u.2.1⟩
  let ix : Fin b.positions.length := (finProdFinEquiv.symm u.2.2).1
  let k := Fin.cast (congrArg (fun z : ReportBundle => z.positions.length) hb) ix
  have h := W.reportMark_fields position origin code siteID edgeID portID next bundle sourceRead j k
  have atIndex : b.positions[ix] = (bundle j).positions[k] := by
    have eq := congrArg (fun z : ReportBundle => z.positions[ix.val]?) hb
    change b.positions[ix.val]? = (bundle j).positions[k.val]? at eq
    rw [List.getElem?_eq_getElem ix.isLt,List.getElem?_eq_getElem k.isLt] at eq
    exact Option.some.inj eq
  change b.positions[ix].parameter = _ ∧ b.positions[ix].place = _
  rw [atIndex]
  exact ⟨h.1,h.2.1⟩

variable (teams : Fin leaves × Fin copies ↪ Fin T) (params : GrammarLabel (Fin n × Bool) (Fin g) n ↪ Fin H)

/-- Genuine global power slot for every chronological reported copy. Its team coordinate
is the original leaf/copy, independently of the current processing team. -/
noncomputable def reportPowerEmbedding :
    UseOccurrence cs ↪ PowerSlot (Fin T) (Fin H) (Nat.clog 2 (r*(2*d.val+1)+1)) :=
  (W.reportUseEquiv position origin code siteID edgeID portID next bundle sourceRead owner team current cs
    cells grouped clone).toEmbedding.trans
    { toFun := fun u => (teams (u.2.val.1,u.1),params u.2.val.2.1,u.2.val.2.2)
      inj' := by
        intro a b h
        have he := teams.injective (congrArg Prod.fst h)
        have hl := params.injective (congrArg (fun z => z.2.1) h)
        have leafEq := congrArg (fun z : Fin leaves × Fin copies => z.1) he
        exact Prod.ext (congrArg Prod.snd he) (Subtype.ext
          (Prod.ext leafEq (Prod.ext hl (congrArg (fun z => z.2.2) h)))) }

/-- The exact injection used by the native clock on an owning-cell dependent tuple.
The only change of coordinates here is the processor's actual cell enumeration. -/
noncomputable def ownedPowerEmbedding (reports : Fin C → List ReportBundle)
    (ordered : ∀ i : Fin cs.length, cs[i].bundles = reports (cells i).val) :
    ((c : {c : Fin C // team c = current}) × UsePositions (reports c.val)) ↪
      PowerSlot (Fin T) (Fin H) (Nat.clog 2 (r*(2*d.val+1)+1)) := by
  let byCell : UseOccurrence cs ≃ ((c : {c : Fin C // team c = current}) × UsePositions (reports c.val)) :=
    (Equiv.sigmaCongrRight fun i => Equiv.cast (congrArg UsePositions (ordered i))).trans (Equiv.sigmaCongrLeft (β := fun c : {c : Fin C // team c = current} => UsePositions (reports c.val)) cells)
  exact byCell.symm.toEmbedding.trans (W.reportPowerEmbedding position origin code siteID edgeID portID next bundle
    sourceRead owner team current cs cells grouped clone teams params)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
