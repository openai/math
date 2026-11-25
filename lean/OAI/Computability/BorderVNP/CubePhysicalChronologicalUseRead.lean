import OAI.Computability.BorderVNP.CubePhysicalReportLedger

/-! # Addressing a numbered power slot at its actual native report occurrence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open DiagonalTallyCellReports DiagonalTallyMaterialize
open scoped Classical

variable {l : ReportLayout}

/-- The physical cursor before this cell and bundle, including all preceding
count fields and listed copies. All four addresses are the ones used by the
native unary operand writer. -/
def occurrenceRead (reports : List (ReportCell l)) (start : ReportCursor) (u : UseOccurrence reports) : UseRead :=
  let cell := reports[u.1]
  let bundle := cell.bundles[u.2.1]
  let q := (reports.take u.1.val).foldl (fun q c => c.after q) start
  let earlier := cell.bundles.take u.2.1.val
  let atBundle := earlier.foldl ReportCursor.afterBundle (q.afterCounts l)
  let atBit := cell.external+cell.supplied+l.gadgets*l.countWidth+(earlier.map ReportBundle.useCount).sum
  let param := atBundle.packed+3*(u.2.2.val/bundle.header.copies)+1
  ⟨param,param+1,atBundle.refs+u.2.2.val,atBit+u.2.2.val,bundle.uses u.2.2⟩

/-- A zero increment at a real report position is equivalent to a false use
bit, since every binary place has positive weight. -/
theorem occurrenceRead_bit {reports : List (ReportCell l)} (start : ReportCursor) (u : UseOccurrence reports)
    (param place : ℕ) (active : Bool)
    (pair : occurrencePair reports u = (param,if active then 2^place else 0)) :
    (occurrenceRead reports start u).bit = active := by
  have value := congrArg Prod.snd pair
  let b := reports[u.1].bundles[u.2.1]
  change (if b.uses u.2.2 then 2^(b.source u.2.2).place else 0) =
    (if active then 2^place else 0) at value
  change b.uses u.2.2=active
  cases h : b.uses u.2.2 <;> cases active <;> simp_all
  exact (Nat.ne_of_lt (Nat.two_pow_pos place)) value

variable {Team Slot : Type*} (owner : Slot → Team) (reports : Team → List (ReportCell l))
    (cursor : Team → ReportCursor) (source : ∀ t,UseOccurrence (reports t) ≃ {i : Slot // owner i=t})

/-- Decode each slot in the report list of the processor that currently owns
its physical site. This retains the actual bit pointer even when that bit is zero. -/
noncomputable def ownedOccurrenceRead (i : Slot) : UseRead :=
  occurrenceRead (reports (owner i)) (cursor (owner i)) ((source (owner i)).symm ⟨i,rfl⟩)

/-- Agreement at each emitted position supplies the native use bit for every
mathematical slot, through the inverse of its actual owning report directory. -/
theorem ownedOccurrenceRead_bit (param place : Slot → ℕ) (active : Slot → Bool)
    (aligned : ∀ t u, let i := (source t u).val
      occurrencePair (reports t) u = (param i,if active i then 2^(place i) else 0))
    (i : Slot) : (ownedOccurrenceRead owner reports cursor source i).bit = active i := by
  let u := (source (owner i)).symm ⟨i,rfl⟩
  have pair := aligned (owner i) u
  dsimp only at pair
  rw [show (source (owner i) u).val=i by exact congrArg Subtype.val ((source (owner i)).apply_symm_apply _)] at pair
  exact occurrenceRead_bit _ u _ _ _ pair

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
