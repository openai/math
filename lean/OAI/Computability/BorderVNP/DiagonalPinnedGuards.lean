import OAI.Computability.BorderVNP.DiagonalNativeCorePaths

/-! # The padded routed domain of the physical private-cell checks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited

variable {D C ns ne np n d blocks b h K s : ℕ} {P Team : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (siteID : N.Site ↪ Fin ns)
    (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (state : Site.Programs N)
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (reports : Fin C → List (List ℕ))

/-- The exact two native padding checks on the shared/private words of a
distributed selector assignment. This is the predicate used by the physical
control-family cut before report and private choices are indexed. -/
def RoutedPins (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (q : Routed (b:=b) (s:=s) owners) : Prop :=
  ∀ i ∉ Set.range slot,readEnd (fun z => Scatter.Assignment.lookup q.2 (.inl z))
    (fun v e j => Scatter.Assignment.lookup q.2 (.inr (.inl (v,e,j)))) false i=false ∧
    readEnd (fun z => Scatter.Assignment.lookup q.2 (.inl z))
      (fun v e j => Scatter.Assignment.lookup q.2 (.inr (.inl (v,e,j)))) true i=false

/-- All proposed original private core vectors at the already pinned routed
assignments. No staging or private cell guard is tested in this domain. -/
abbrev PinnedRaw := {q : Routed (b:=b) (s:=s) owners // RoutedPins N cell owners slot q} ×
  ((c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)

theorem routedPins_iff (q : Routed (b:=b) (s:=s) owners)
    (z : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool) :
    RoutedPins N cell owners slot q ↔ Path.Pins N cell slot (rawPath N cell edgeID state owners q z) := Iff.rfl

local notation3 (prettyPrint := false) "guard" => GuardedCores N cell siteID edgeID portID state owners slot ports owner reports

/-- Subtotal address lists are consumed by the subsequent count check.
The endpoint and local factor guards depend only on the private bank,
the factor boxes, and their ordered records. -/
theorem guardedCores_report_irrel (other : Fin C → List (List ℕ))
    (a : Routed (b := b) (s := s) owners) (z : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool) :
    guard a z ↔ GuardedCores N cell siteID edgeID portID state owners slot ports owner other a z := Iff.rfl

/-- The successful private directory already certifies the endpoint padding of
its routed input. Forgetting the repeated proof preserves both the whole routed
assignment and the original unchecked bank on each physical cell. -/
def pinnedGuardsEquiv :
    {a : PinnedRaw (s := s) N cell state owners slot // guard a.1.val a.2} ≃
      {a : Routed (b:=b) (s:=s) owners × ((c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool) //
        guard a.1 a.2} where
  toFun a := ⟨(a.val.1.val,a.val.2),a.property⟩
  invFun a := ⟨(⟨a.val.1,(routedPins_iff N cell edgeID state owners slot a.val.1 a.val.2).mpr a.property.1⟩,a.val.2),a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
