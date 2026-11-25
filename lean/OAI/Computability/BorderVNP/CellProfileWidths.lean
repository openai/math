import OAI.Computability.BorderVNP.CellSparse

/-! # Selector-width bounds for public profile records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- The binary selector has at most one lane per explicitly supplied histogram entry. -/
def Record.ProfileWidthOK : Record → Prop
  | .profile _ _ w hist _ => w ≤ hist.length
  | _ => True

/-- Bound the number of selector-lane descriptors by the stored number of terms. -/
def Record.clipProfile : Record → Record
  | .profile c p w hist rs => .profile c p (min hist.length w) hist rs
  | r => r

/-- Width clipping fixes every admissible source record. -/
theorem Record.clipProfile_eq (r : Record) (hr : r.ProfileWidthOK) : r.clipProfile = r := by
  cases r with
  | profile c p w hist rs => simp [clipProfile, Nat.min_eq_right (show w ≤ hist.length from hr)]
  | zero | equal | box => rfl

/-- All selector widths in the directory can be recovered in unary from its stored histograms. -/
def Directory.ProfileWidths (D : Directory) : Prop := ∀ r ∈ D.records, r.ProfileWidthOK

/-- Directory whose public profile records have their widths clipped to the number of terms. -/
def Directory.clipProfiles (D : Directory) : Directory := {D with records := D.records.map Record.clipProfile}

/-- The complete native emitter produces the original public guard sequence on admissible data. -/
theorem Directory.clipProfiles_eq (D : Directory) (hd : D.ProfileWidths) : D.clipProfiles = D := by
  have hr : D.records.map Record.clipProfile = D.records := by
    simpa using List.map_congr_left (g := id) (fun r h => r.clipProfile_eq (hd r h))
  unfold clipProfiles
  rw [hr]

end CellSparse

end BorderVNP
end Computability
end OAI
