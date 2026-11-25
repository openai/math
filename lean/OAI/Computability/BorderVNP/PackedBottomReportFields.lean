import OAI.Computability.BorderVNP.PackedBottomReportCursors
import OAI.Computability.BorderVNP.CellPacketFieldMonotone
import OAI.Computability.BorderVNP.CellProfileWidths

/-! # Numeric and static bounds on the original-weight report supplement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse

set_option maxRecDepth 12000

/-- Supplemental rows are exactly wiring tests, with no new table traversal. -/
def Wiring : Record → Prop
  | .zero .. | .equal .. => True
  | _ => False

private theorem links_wiring (base stride copies cursor : ℕ) (ps : List (Port × ℕ)) :
    ∀ r ∈ links base stride copies cursor ps, Wiring r := by
  induction ps generalizing cursor with
  | nil => simp [links]
  | cons a ps ih =>
    rcases a with ⟨p,rel⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl|hr
    · trivial
    · exact ih _ r hr

/-- Only equality and zero rows appear in the final appended list. -/
theorem supplements_wiring (start : ℕ) (bs : List Bundle) : ∀ r ∈ supplements start bs, Wiring r := by
  induction bs generalizing start with
  | nil => simp [supplements]
  | cons x bs ih =>
    intro r hr
    rcases List.mem_append.mp hr with hx | ht
    · rcases List.mem_append.mp hx with hl | hz
      · exact links_wiring _ _ _ _ _ r hl
      · rw [List.mem_singleton] at hz
        subst r
        trivial
    · exact ih _ r ht

/-- Each extra test contributes a fixed public record cost, regardless of its
copy count, local stride or original gadget position. -/
theorem wiring_nodes (rs : List Record) (h : ∀ r ∈ rs, Wiring r) :
    Directory.recordNodes rs = 1025*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hm : r.guardMassBound = 1024 := by
      have hw := h r List.mem_cons_self
      cases r <;> first | rfl | cases hw
    have t := ih (fun x hx => h x (.tail _ hx))
    simp only [Directory.recordNodes,List.length_cons,List.map_cons,List.sum_cons,hm] at t ⊢
    omega

/-- The largest supplemental record has nine scalar fields. -/
theorem wiring_words {r : Record} (h : Wiring r) : (Packet.record r).length ≤ 9 := by
  cases r with
  | zero => exact (by decide : 6 ≤ 9)
  | equal => exact le_refl 9
  | _ => cases h

theorem wiring_profile {r : Record} (h : Wiring r) : r.ProfileWidthOK := by
  cases r <;> trivial

private theorem links_fields (base stride copies cursor V : ℕ) (ps : List (Port × ℕ)) (h₁ : 1 ≤ V)
    (hstride : stride ≤ V) (hcopies : copies ≤ V) (hcursor : cursor+ps.length*copies ≤ V)
    (hrel : ∀ p ∈ ps, base+p.2 ≤ V) : ∀ r ∈ links base stride copies cursor ps, Packet.RecordFields r V := by
  induction ps generalizing cursor with
  | nil => simp [links]
  | cons p ps ih =>
    rcases p with ⟨p,rel⟩
    rw [List.length_cons,Nat.succ_mul] at hcursor
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨⟨hcopies,h₁,⟨hrel _ List.mem_cons_self,hstride,h₁⟩,⟨show cursor ≤ V by omega,h₁,h₁⟩⟩,trivial⟩
    · exact ih (cursor+copies) (by omega) (fun p hp => hrel p (.tail _ hp)) _ hr

private theorem report_fields (x : Bundle) (start V : ℕ) (one : 1 ≤ V) (end_ : start+x.useBits ≤ V)
    (hc : count x.factors ≤ x.header.cap) (hcopies : x.header.copies ≤ V)
    (hbox : x.header.boxBase+x.header.orig+x.header.cap ≤ V) :
    ∀ r ∈ reportRows x.header.boxBase x.header.orig x.header.cap x.header.copies start x.factors,
      Packet.RecordFields r V := by
  intro r hr
  rcases List.mem_append.mp hr with hl | hz
  · apply links_fields _ _ _ _ _ _ one (by dsimp only [bottomStride]; omega) hcopies _ _ r hl
    · rw [sidecar_length]; exact end_
    · intro a ha
      have hmem : a.2 ∈ List.range' x.header.orig (count x.factors) := by
        rw [← sidecar_ranks]
        exact List.mem_map.mpr ⟨a,ha,rfl⟩
      obtain ⟨i,hi,he⟩ := List.mem_range'.mp hmem
      simp only [Nat.one_mul] at he
      omega
  · rw [List.mem_singleton] at hz
    subst r
    exact ⟨⟨hcopies,by omega,⟨by dsimp only [stagedPort,padding]; omega,
      by dsimp only [stagedPort,padding,bottomStride]; omega,one⟩⟩,trivial⟩

/-- Every actual native supplemental scalar, including the unused suffix
address at a zero-width or zero-copy box, satisfies the local numeric bound.
The hypotheses separately bound the one-copy allocation and the true compact
external-use cursor. -/
theorem supplements_recordFields (start : ℕ) (bs : List Bundle) (V : ℕ) (one : 1 ≤ V)
    (end_ : nextCursor start bs ≤ V)
    (h : ∀ x ∈ bs, count x.factors ≤ x.header.cap ∧ x.header.copies ≤ V ∧
      x.header.boxBase+x.header.orig+x.header.cap ≤ V) :
    ∀ r ∈ supplements start bs, Packet.RecordFields r V := by
  induction bs generalizing start with
  | nil => simp [supplements]
  | cons x bs ih =>
    obtain ⟨hc,hcopy,hbox⟩ := h x List.mem_cons_self
    rw [nextCursor_cons] at end_
    have hstart : start+x.useBits ≤ V := (Nat.le_add_right _ _).trans end_
    intro r hr
    rcases List.mem_append.mp hr with hrow|ht
    · exact report_fields x start V one hstart hc hcopy hbox _ hrow
    · exact ih _ end_ (fun y hy => h y (.tail _ hy)) _ ht

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
