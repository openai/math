import OAI.Computability.BorderVNP.CellPacketFields
import Mathlib.Data.List.GetD

/-! # Relocating site-local box references into the merged cell directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Move the box ordinal into its cell-wide interval. All physical wire addresses,
copy counts, strides, selector data and route descriptions stay on the same rows. -/
def Record.rebaseBox (offset : ℕ) : Record → Record
  | .box id base copies stride => .box (offset+id) base copies stride
  | r => r

/-- Every reference made by this row belongs to the given box directory. -/
def Record.BoxRefFits (r : Record) (len : ℕ) : Prop :=
  match r with
  | .box id .. => id < len
  | _ => True

/-- Prefix relocation maps each valid local ordinal into the enlarged directory. -/
theorem Record.rebaseBox_refFits (r : Record) {offset n total : ℕ} (h : r.BoxRefFits n)
    (span : offset+n ≤ total) : (r.rebaseBox offset).BoxRefFits total := by
  cases r <;> simp_all [rebaseBox,BoxRefFits]; omega

/-- The public guard's structural weight is independent of the numerical box ordinal. -/
theorem Record.rebaseBox_guardMassBound (r : Record) (offset : ℕ) :
    (r.rebaseBox offset).guardMassBound = r.guardMassBound := by cases r <;> rfl

/-- At a common numeric field scale, valid local ordinals remain within range after
prefix relocation. The other scalar and list fields retain their original bounds. -/
theorem Packet.recordFields_rebaseBox (r : Record) {offset n U : ℕ} (h : RecordFields r U)
    (href : r.BoxRefFits n) (span : offset+n ≤ U+1) : RecordFields (r.rebaseBox offset) U := by
  cases r with
  | box id base copies stride =>
    obtain ⟨_,_,hb,hc,hs⟩ := h
    change id < n at href
    exact ⟨trivial, by omega, hb, hc, hs⟩
  | _ => exact h

/-- Rebase all rows of one site against the common box table. -/
def Directory.rebaseBoxes (D : Directory) (merged : List (List Factor)) (offset : ℕ) : Directory :=
  ⟨merged,D.records.map (Record.rebaseBox offset),D.reportedCounts⟩

/-- Relocated ordinals select the original one-copy factors, including in a directory
assembled by an arbitrary stable site scan. The factor sweeps therefore retain their
physical bases, multiplicities, strides, local order, and signed table contents. -/
theorem Directory.blocks_rebaseBoxes_of_getD (D : Directory) (merged : List (List Factor)) (offset : ℕ)
    (h : ∀ r ∈ D.records, r.BoxRefFits D.boxes.length)
    (get : ∀ i < D.boxes.length, merged.getD (offset+i) [] = D.boxes.getD i []) :
    (D.rebaseBoxes merged offset).blocks = D.blocks := by
  simp only [rebaseBoxes,blocks,List.filterMap_map]
  apply List.filterMap_congr
  intro r hr
  cases r with
  | box id base copies stride =>
    have eq := get id (h _ hr)
    change some (⟨base,copies,stride,merged.getD (offset+id) []⟩ : BoxBlock) =
      some ⟨base,copies,stride,D.boxes.getD id []⟩
    rw [eq]
  | _ => rfl

/-- Every local block is resolved identically after inserting earlier and later
sites into the cell packet. The ordinal offset is exactly the preceding list length. -/
theorem Directory.blocks_rebaseBox (D : Directory) (pre post : List (List Factor))
    (h : ∀ r ∈ D.records, r.BoxRefFits D.boxes.length) :
    (D.rebaseBoxes (pre ++ D.boxes ++ post) pre.length).blocks = D.blocks := by
  apply D.blocks_rebaseBoxes_of_getD _ _ h
  intro i hi
  rw [List.append_assoc,List.getD_append_right _ _ _ _ (Nat.le_add_right ..),
    Nat.add_sub_cancel_left,List.getD_append _ _ _ _ hi]

/-- The list of public record validity checks before and after relocation agrees on
every physical bank. A valid reference still denotes an actual directory entry. -/
theorem Directory.records_valid_rebaseBoxes (D : Directory) (merged : List (List Factor)) (offset : ℕ)
    (bank : ℕ → Bool) (h : ∀ r ∈ D.records, r.BoxRefFits D.boxes.length)
    (span : offset+D.boxes.length ≤ merged.length) :
    (∀ r ∈ (D.rebaseBoxes merged offset).records, r.Valid merged bank) ↔
      ∀ r ∈ D.records, r.Valid D.boxes bank := by
  have hr (r : Record) (hm : r ∈ D.records) : (r.rebaseBox offset).Valid merged bank ↔ r.Valid D.boxes bank := by
    cases r with
    | box id base copies stride =>
      have hi : id < D.boxes.length := h _ hm
      change offset+id < merged.length ↔ id < D.boxes.length
      omega
    | _ => rfl
  constructor
  · intro yes r hm; exact (hr r hm).mp (yes _ (List.mem_map.mpr ⟨r,hm,rfl⟩))
  · intro yes r hm
    change r ∈ D.records.map (Record.rebaseBox offset) at hm
    obtain ⟨orig,horig,rfl⟩ := List.mem_map.mp hm
    exact (hr orig horig).mpr (yes orig horig)

/-- The site contribution to the signed cell weight is invariant under genuine
prefix rebasing, with identical incoming physical bits and advertised subtotals. -/
theorem Directory.weight_rebaseBox (D : Directory) (pre post : List (List Factor)) (bank : ℕ → Bool)
    (h : ∀ r ∈ D.records, r.BoxRefFits D.boxes.length) :
    (D.rebaseBoxes (pre ++ D.boxes ++ post) pre.length).weight bank = D.weight bank := by
  let E := D.rebaseBoxes (pre ++ D.boxes ++ post) pre.length
  have ho : E.occurrences = D.occurrences := by
    rw [← E.blocks_visits,← D.blocks_visits]
    exact congrArg (List.flatMap BoxBlock.visits) (D.blocks_rebaseBox pre post h)
  have hv := D.records_valid_rebaseBoxes (pre ++ D.boxes ++ post) pre.length bank h (by simp)
  change E.weight bank = D.weight bank
  unfold Directory.weight Directory.observations
  rw [ho]
  change (∀ r ∈ E.records, r.Valid E.boxes bank) ↔ _ at hv
  cases D.occurrences.mapM (fun occ => occ.factor.observe bank occ.offset occ.copy) with
  | none => rfl
  | some obs =>
    dsimp only
    by_cases cond : (∀ r ∈ D.records, r.Valid D.boxes bank) ∧ countsValid bank D.reportedCounts obs
    · have yes : (∀ r ∈ E.records, r.Valid E.boxes bank) ∧ countsValid bank E.reportedCounts obs :=
        ⟨hv.mpr cond.1,cond.2⟩
      rw [ite_eq_left yes, ite_eq_left cond]
    · have no : ¬ ((∀ r ∈ E.records, r.Valid E.boxes bank) ∧ countsValid bank E.reportedCounts obs) :=
        fun yes => cond ⟨hv.mp yes.1,yes.2⟩
      rw [ite_eq_right no, ite_eq_right cond]

end CellSparse

end BorderVNP
end Computability
end OAI
