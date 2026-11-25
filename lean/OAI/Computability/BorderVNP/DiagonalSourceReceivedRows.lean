import OAI.Computability.BorderVNP.DiagonalPositiveReportMap
import OAI.Computability.BorderVNP.DiagonalRoutedSourceReports
import Mathlib.Data.List.NodupEquivFin

/-! # Global cell order of the report rows fixed by a routed cube -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open Cube.Physical.NativeAssignments

variable {C T J : ℕ} (layout : Fin T → ReportLayout) (home : Fin J → Fin C)
    (payload : Fin J → ReportBundle) (team : Fin C → Fin T) (who : ℕ → ℕ)
    (assigned : ∀ c : Fin C,who c.val=(team c).val) (bank supply privateWidth : ℕ → ℕ)
    (digits : ∀ u : Fin T, ℕ → Fin (layout u).gadgets → Fin (layout u).countWidth → Bool)

private abbrev owned (u : Fin T) := (List.range C).filter fun c => decide (who c=u.val)

private def ownedMembership (u : Fin T) :
    {j : ℕ // j ∈ owned (C:=C) who u} ≃ {c : Fin C // team c=u} where
  toFun j := by
    have h := List.mem_filter.mp j.property
    let c : Fin C := ⟨j.val,List.mem_range.mp h.1⟩
    exact ⟨c,Fin.ext ((assigned c).symm.trans (of_decide_eq_true h.2))⟩
  invFun c := ⟨c.val.val,List.mem_filter.mpr ⟨List.mem_range.mpr c.val.isLt,
    decide_eq_true ((assigned c.val).trans (congrArg Fin.val c.property))⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

local notation3 (prettyPrint := false) "issued(" u ")" => sourceCells (layout u) home payload (Fin.val u) who bank supply privateWidth (digits u)

private noncomputable def sourceLocalOrder (u : Fin T) :
    Fin (issued(u)).length ≃ {c : Fin C // team c=u} :=
  (finCongr (List.length_map _)).trans ((List.Nodup.getEquiv (owned (C:=C) who u) (List.Nodup.filter _ List.nodup_range)).trans
    (ownedMembership team who assigned u))

/-- A fixed filtered report directory already indexes every cell exactly once,
in its selected owner's original ordinal order. The equivalence also covers
empty teams and cells containing zero bundles. -/
noncomputable def receivedSourceRows : ReceivedRows layout C where
  cells u := issued(u)
  order := (Equiv.sigmaCongrRight (sourceLocalOrder layout home payload team who assigned bank supply privateWidth digits)).trans
    (Equiv.sigmaFiberEquiv team)
  number u i := by
    change ((issued(u)).get i).number = (sourceLocalOrder layout home payload team who assigned bank supply privateWidth digits u i).val.val
    let f := sourceCell (layout u) home payload bank supply privateWidth (digits u)
    have bound : i.val < ((owned (C := C) who u).map f).length := i.isLt
    exact congrArg ReportCell.number (List.getElem_map f (l := owned (C := C) who u) (h := bound))

/-- The owner computed from the selected cube coordinates agrees with the
team indexing each of these globally numbered source rows. -/
theorem receivedSourceRows_owner (u : Fin T)
    (i : Fin ((receivedSourceRows layout home payload team who assigned bank supply privateWidth digits).cells u).length) :
    team ((receivedSourceRows layout home payload team who assigned bank supply privateWidth digits).order ⟨u,i⟩)=u :=
  (sourceLocalOrder layout home payload team who assigned bank supply privateWidth digits u i).property

end DiagonalTallyCellReports.ReportDirectory

namespace RoutingISA.Evaluator.SignedPrep

open Crossing CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments
open DiagonalTallyCellReports ReportDirectory

variable {D R bundles : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (ar : CubeArena.Layout) (N : Network D P bits) (cell : N.Site → Fin ar.cells)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (slot : LiveBit N cell ↪ Slot ar.n ar.header.d ar.header.blocks (ar.h*ar.b))
    (label : Fin ar.cells → Label (ar.n+1) ar.header.d)
    (charts : Fin (R+1) → ReportLayout) (home : Fin bundles → Fin ar.cells) (bodies : Fin bundles → ReportBundle)
    (supplied wires : ℕ → ℕ) (q : Routed (b := ar.b) (s := ar.s) owners)

/-- The seeded cube's report directory, before any private bank, per-cell
report or global subtotal is sampled. Its team rows are exactly those
decoded by the actual routed preparation equivalence. -/
noncomputable def routedReceivedRows : ReceivedRows charts ar.cells :=
  receivedSourceRows charts home bodies (fun c => owners q.1 (label c (chosen ar.b ar.s q.1)))
    (routedOwnerWord ar owners label q) (routedOwnerWord_at ar owners label q)
    (fun c => ar.cellBank+c*ar.cellStride) supplied wires (fun _ _ _ _ => false)

omit [Fintype P] in
theorem routedReceivedRows_cells (u : Fin (R+1)) :
    (routedReceivedRows ar owners label charts home bodies supplied wires q).cells u =
      (routedSourceReports ar N cell owners slot label charts home bodies supplied wires).cells q u := rfl

/-- Regroup the report returns over all actual teams on this routed selector
as the reports of these very same source cells. -/
def routedReportAssignments :
    (routedSourceReports ar N cell owners slot label charts home bodies supplied wires).actual q ≃
    ((u : Fin (R+1)) → ReportAssignments ((routedReceivedRows ar owners label charts home bodies supplied wires q).cells u)) :=
  Equiv.refl _

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
