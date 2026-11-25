import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceSite
import OAI.Computability.BorderVNP.PackedInheritedMergedPacket
import OAI.Computability.BorderVNP.RoutingISASparseCells

/-! # The actual merged finite cell packet and its bit-major field reports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Merged

open VPVNP Crossing Packing Packing.CellAddresses Packing.Inherited CellSparse
open FiniteDiagonal.CellTrace RoutingISA RoutingISA.CompactMachine
open scoped BigOperators Classical

variable {D M np ns : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns)
  (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np) (state : N.Site → Site)

/-- The actual physical owned-cell table treated as one inherited site. Its
private extent contains the real within-cell wires and all fully staged
work slabs, and its external extent contains just the delivered endpoints. -/
noncomputable def site : Site :=
  let D := Placement.packet N cell c siteID edgeID portID state []
  ⟨externalBase N cell c (fun v => (state v).size),suppliedSize N cell c,D.boxes,[D.records]⟩

/-- The synthetic site's directory is exactly the real rebased and merged
geometry packet before supplying its finite scalar-report addresses. -/
theorem directory_eq :
    (site N cell c siteID edgeID portID state).directory =
      Placement.packet N cell c siteID edgeID portID state [] := by
  simp [site,Site.directory,Site.rows,Placement.packet,Directory.mergeSites]

/-- Attaching the chronological bit-major report metadata does not change
any inherited box byte or private wire interval. -/
theorem report_directory (scalars digits : ℕ) :
    PackedSite.directory (site N cell c siteID edgeID portID state) scalars digits =
      Placement.packet N cell c siteID edgeID portID state
        (Reports.fields (site N cell c siteID edgeID portID state).size scalars digits) := by
  unfold PackedSite.directory
  rw [directory_eq]
  rfl

section
variable {F : Type*} [Field F] [Fintype F] (s : Site) (digits : ℕ)

/-- The actual compact native validator inputs, including the chronological
bit-major scalar report after the original delivered fields. -/
noncomputable def validator (x : Fin s.incoming → Bool) (report : Fin (Fintype.card F) → Fin digits → Bool) : CellInput :=
  ⟨PackedSite.directory s (Fintype.card F) digits,s.work,PackedSite.external s x report⟩

/-- The actual field product read by the fixed scalar routine from this
particular matrix of count bits. -/
noncomputable def reportScalar (report : Fin (Fintype.card F) → Fin digits → Bool) : F :=
  ∏ v, (Fintype.equivFin F).symm v ^ FieldPowers.digits (List.ofFn (report v))

/-- Summing the signed validator times the real scalar-return value over
all physical reports restores exactly the original site's full value. -/
theorem sum_validator (locality : s.Local) (x : Fin s.incoming → Bool)
    (range : ∀ (g : Fin s.work → Bool) obs, s.observe (Inherited.bits g x) = some obs → ∀ j ∈ obs.filterMap Prod.snd, j < Fintype.card F)
    (fit : ∀ (g : Fin s.work → Bool) obs, s.observe (Inherited.bits g x) = some obs → (obs.filterMap Prod.snd).length < 2^digits) :
    (∑ report : Fin (Fintype.card F) → Fin digits → Bool,
      ((validator s digits x report).weight : F) * reportScalar digits report) =
      s.value (fieldWeight (FieldPowers.entry (Fintype.equivFin F).symm)) x := by
  change (∑ report : Fin (Fintype.card F) → Fin digits → Bool,
    ((∑ g : Fin s.work → Bool, (PackedSite.directory s (Fintype.card F) digits).weight
      (lookup (List.ofFn g ++ PackedSite.external s x report)) : ℤ) : F) * reportScalar digits report) = _
  simp only [Int.cast_sum,Finset.sum_mul,reportScalar]
  rw [Finset.sum_comm]
  have eq := PackedSite.site_field (F := F) s (digits := digits) locality x range fit
  simpa only [Compact.assignmentTails_sum] using eq

end
end FiniteEvaluator.Merged

end BorderVNP
end Computability
end OAI
