import OAI.Computability.BorderVNP.PackedBottomReportCursors
import OAI.Computability.BorderVNP.PackedGridReportedUse

/-! # Physical compact report bits and the original verifier's named uses

The sparse scanner orders reports by the private weighted list. Resolving that
list at a copy recovers the named use of the corresponding fine rule. A passing
rewired unary vertex therefore supplies exactly its original power-word bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing GridBoxes CellSparse
open scoped Classical

/-- A fine factor reads relative wires from its box. Unary source names are
resolved through the use-bit stream at this copy. -/
def namedRead (bank : ℕ → Bool) (off copy : ℕ) (use : Port → Bool) : Factor → Option (Bool × Option ℕ)
  | .unary wire tag => if bank (off+wire) = use tag then some (false,none) else none
  | f => f.observe bank off copy

/-- The kth source of the sidecar resolves to its own use bit in this copy. -/
def NamedAt (bank : ℕ → Bool) (use : Port → Bool) (copies copy : ℕ) :
    ℕ → List (Port × ℕ) → Prop
  | _, [] => True
  | cursor, (tag,_) :: ps => bank (cursor+copy) = use tag ∧ NamedAt bank use copies copy (cursor+copies) ps

/-- The list of expanded private reads at this copy is the genuine named source
calculation whenever the scanner's per-row use bits are the indicated values. -/
theorem compactReads_named (bank : ℕ → Bool) (use : Port → Bool) (off copies copy next cursor : ℕ)
    (fs : List Factor) (h : NamedAt bank use copies copy cursor (sidecar next fs)) :
    compactReads bank off copy copies cursor fs = fs.map (namedRead bank off copy use) := by
  induction fs generalizing next cursor with
  | nil => rfl
  | cons f fs ih =>
    cases f with
    | truth | sign | gadget => simp [compactReads,namedRead,ih next cursor (by simpa [sidecar] using h)]
    | unary wire tag =>
      simp only [sidecar,NamedAt] at h
      simp [compactReads,namedRead,h.1,ih _ _ h.2]

/-- At an actual original vertex this comparison is exactly the verifier's specified
local rule on its named incidence lanes. -/
theorem rule_read {D : ℕ} {P C : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → C) (c : C) {m n : ℕ} (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (v : {v : N.Site // cell v = c}) (order : CellBox.Lane N v.val ≃ Fin (Fintype.card (CellBox.Lane N v.val)))
    (r : Rule N v.val) (bank : ℕ → Bool) (off copy : ℕ) (use : Port → Bool) :
    namedRead bank off copy use (ruleFactor N cell c edgeID portID v order r) =
      if r.passes (fun l => bank (off+(lane N cell c edgeID portID v l).val)) use
      then some (false,none) else none := by
  cases r with
  | truth f =>
    change (ruleFactor N cell c edgeID portID v order (.truth f)).observe bank off copy = _
    rw [observe_rule,accepts_passes]
    rfl
  | unary l t => simp [namedRead,ruleFactor,Rule.passes]

/-- On the physical staged directory all fine vertices of the named cell read
exactly their original guard, including the chosen unary input. -/
theorem staged_grid_reads {D : ℕ} {P C : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → C) (c : C) {m n s : ℕ} (siteID : N.Site ↪ Fin s)
    (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n) (rules : ∀ v : {v : N.Site // cell v = c}, Rule N v.val)
    (bank : ℕ → Bool) (boxes : List (List Factor)) (use : Port → Bool) (base stride copies copy next cursor : ℕ)
    (hi : copy < copies) :
    let fs := factors N cell c siteID edgeID portID rules
    (∀ r ∈ links base stride copies cursor (sidecar next fs), r.Valid boxes bank) →
    NamedAt bank use copies copy cursor (sidecar next fs) →
    (stage next fs).map (fun f => f.observe bank (base+copy*stride) copy) =
      (siteList N cell c siteID).map (fun v =>
        if (rules v).passes (fun l => bank ((base+copy*stride)+(lane N cell c edgeID portID v l).val)) use
        then some (false,none) else none) := by
  intro fs hl hn
  rw [stage_observe bank boxes base stride copies copy hi next cursor fs hl,
    compactReads_named bank use (base+copy*stride) copies copy next cursor fs hn]
  simp only [fs,factors,List.map_map,Function.comp_def,rule_read]

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
