import OAI.Computability.BorderVNP.DiagonalTallyReportBundleLoop
import OAI.Computability.BorderVNP.CellTeamExteriorCharge
import OAI.Computability.BorderVNP.CellPacketSupplementalCost
import OAI.Computability.BorderVNP.DiagonalPowerWords

/-! # The sizes of the true supplemental cell reports in Section 11

There is one equality record per listed position in a delivered bottom-bundle
description and one padding row. Repetition enters the use-bit bank through
actual original power occurrences. Each count bit already has its own public
address word in the geometry packet.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open Cube.TeamRowClock RoutingISA CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source
open Packing.BottomReports
open scoped Classical

/-- The exact ordered list of supplemental records produced by the original-bundle
loop. Each successive bundle reads the updated private-use cursor. -/
def bindingRows : List ReportBundle → LocalReportCursor → List Record
  | [],_ => []
  | b::bs,q => b.rows q ++ bindingRows bs (q.advance b)

/-- The native row writer emits nine public words per actual listed position and
six for the one bundle padding row, with no repetition of that row stream. -/
theorem binding_words (bs : List ReportBundle) (q : LocalReportCursor) :
    ((bindingRows bs q).flatMap record).length = (bs.map fun b => 9*b.positions.length+6).sum := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih =>
    rw [bindingRows,List.flatMap_append,List.length_append,ih,List.map_cons,List.sum_cons]
    congr 1
    rw [ReportBundle.rows,List.flatMap_append,List.length_append,Writer.Frame.rows_words_length]
    rfl

/-- Reading a genuine sidecar controls its marked position count even if a bundle
has zero expanded copies. -/
theorem ReportBundle.Input.marked_le {w desc p : ℕ} {l : ReportLayout} {b : ReportBundle}
    {q : LocalReportCursor} {m : ℕ → ℕ} (data : b.Input (w:=w) l q p desc m) :
    b.positions.length ≤ desc := by
  have room := data.descriptionRoom
  rw [TallySidecar.bits_length] at room
  by_cases h : l.fieldWidth = 0
  · have f := data.values b.positions.length (by simp [TallySidecar.fields])
    rw [h] at f
    omega
  · have hc := Nat.le_mul_of_pos_left (1+3*b.positions.length) (show 0 < l.fieldWidth by omega)
    omega

/-- The supplemental word count can be charged to the original delivered string
once per bottom bundle. The bound also covers an empty marked-position list. -/
theorem binding_words_le {w desc : ℕ} (l : ReportLayout) (bs : List ReportBundle)
    (q : LocalReportCursor) (p : ℕ) (m : ℕ → ℕ) (input : bundleInputs w l desc bs q p m) :
    ((bindingRows bs q).flatMap record).length ≤ 9*(desc+1)*bs.length := by
  rw [binding_words]
  induction bs generalizing q p m with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨h,rest⟩ := input
    have bound := h.marked_le
    have tail := ih _ _ _ rest
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [Nat.mul_succ (9*(desc+1))]
    exact Nat.add_le_add (by omega : 9*b.positions.length+6 ≤ 9*(desc+1)) tail |>.trans_eq (Nat.add_comm ..)

/-- The genuine one-copy count vectors' digit addresses are already public
words in the cell packet, independently of its other records and hidden boxes. -/
theorem count_digits_le_public {Site : Type} (p : Placed Site) :
    (p.reports.map List.length).sum ≤ (p.parts.flatMap Part.publicBuffer).length := by
  have bound (rs : List (List ℕ)) : (rs.map List.length).sum ≤ (fieldList vector rs).length := by
    induction rs with
    | nil => simp [fieldList]
    | cons r rs ih =>
      simp only [fieldList,List.flatMap_cons,List.length_cons,List.length_append,vector,List.map_cons,List.sum_cons] at ih ⊢
      omega
  have h := bound p.reports
  simp only [Placed.parts,plan,List.flatMap_cons,List.flatMap_append,List.flatMap_nil,Part.publicBuffer,
    List.length_append,List.length_cons,List.length_nil,List.append_nil]
  omega

/-- True report-use bits of a group of bundles, indexed by their physical bundle
ordinal and the position/copy ordinal consumed by its native writer. -/
abbrev UsePositions (bs : List ReportBundle) := (j : Fin bs.length) × Fin bs[j.val].useCount

/-- Counting these actual occurrence indices gives exactly the allocated use-bit width. -/
theorem use_card (bs : List ReportBundle) :
    Fintype.card (UsePositions bs) = (bs.map ReportBundle.useCount).sum := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin,←List.sum_ofFn]
  rw [List.ofFn_getElem_eq_map bs ReportBundle.useCount]

/-- A distinct original power slot pays each checked per-copy use bit. This
bound includes all batches, parameters and binary places in their original order. -/
theorem owned_use_le {C T H B : ℕ} (owner : Fin C → ℕ) (team : ℕ) (bs : Fin C → List ReportBundle)
    (original : ((c : {c : Fin C // owner c=team}) × UsePositions (bs c.val)) ↪
      Diagonal.CellEntries.PowerSlot (Fin T) (Fin H) B) :
    assignedSum owner team (fun c => ((bs c).map ReportBundle.useCount).sum) ≤ T*(H*B) := by
  have card := Fintype.card_le_of_injective original original.injective
  rw [Fintype.card_sigma] at card
  simp only [use_card,Diagonal.CellEntries.PowerSlot,Fintype.card_prod,Fintype.card_fin] at card
  change ∑ c : Fin C, (if owner c=team then ((bs c).map ReportBundle.useCount).sum else 0) ≤ _
  rw [←Finset.sum_filter,Finset.sum_subtype (p:=fun c => owner c=team) _ (fun _ => by simp) _]
  exact card

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
