import OAI.Computability.BorderVNP.PackedBottomReportFields

/-! # Transport of complete cell resources through the weighted-source append -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse

/-- The typed payload reconstructed by the supplemental writer. -/
def appendRows (D : Directory) (extra : List Record) : Directory :=
  {D with records := D.records ++ extra}

private theorem append_blocks (D : Directory) (extra : List Record) (h : ∀ r ∈ extra, Wiring r) :
    (appendRows D extra).blocks = D.blocks := by
  unfold Directory.blocks appendRows
  rw [List.filterMap_append]
  have he : extra.filterMap (fun r => match r with
    | Record.box id base copies stride => some (⟨base,copies,stride,D.boxes.getD id []⟩ : BoxBlock)
    | _ => none) = [] := List.filterMap_eq_nil_iff.mpr (fun r hr => by
      have hw := h r hr
      cases r <;> first | rfl | cases hw)
  exact (congrArg (_ ++ ·) he).trans (List.append_nil _)

/-- Appending genuine wiring costs only its static record mass and leaves
every table traversal, subtotal width and original private factor unchanged. -/
theorem append_static {D : Directory} {M : ℕ} (hD : D.StaticBounds 1026 M)
    (extra : List Record) (h : ∀ r ∈ extra, Wiring r) (hlen : extra.length ≤ 2*(M+1)) :
    (appendRows D extra).StaticBounds 3076 M := by
  have sq : M+1 ≤ (M+1)^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right (M+1) (Nat.succ_pos _)
  have grow : (appendRows D extra).recordMass = D.recordMass+Directory.recordNodes extra := by
    simp only [appendRows,Directory.recordMass,Directory.recordNodes,List.length_append,List.map_append,List.sum_append]
    omega
  refine ⟨?_,?_,hD.3.trans (Nat.mul_le_mul_right _ (by decide)),hD.4.trans (Nat.mul_le_mul_right _ (by decide))⟩
  · rw [grow,wiring_nodes extra h]
    have he := Nat.mul_le_mul_left 1025 (hlen.trans (Nat.mul_le_mul_left _ sq))
    have hd := hD.1
    omega
  · change sweepMass _ (appendRows D extra).blocks ≤ _
    rw [append_blocks D extra h]
    exact hD.2.trans (Nat.mul_le_mul_right _ (by decide))

/-- Local generator fields and original packet fields obey their respective
limits for the post-supplement payload. -/
theorem append_fields {D : Directory} {p V U : ℕ} (hc : D.CompactFields p V) (hr : Packet.RawFields D p U)
    (hVU : V ≤ U) (extra : List Record) (h : ∀ r ∈ extra, Wiring r)
    (he : ∀ r ∈ extra, Packet.RecordFields r V) (hrows : D.records.length+extra.length ≤ U) :
    (appendRows D extra).CompactFields p V ∧ Packet.RawFields (appendRows D extra) p U := by
  have b := append_blocks D extra h
  refine ⟨⟨hc.privateWires,?_,?_,?_,hc.reports⟩,
    ⟨hr.privateWires,⟨hr.lengths.1,by simpa only [appendRows,List.length_append] using hrows,hr.lengths.2.2⟩,
      hr.boxes,?_,hr.reports⟩⟩
  · change ((appendRows D extra).blocks.map _).sum ≤ _
    rw [b]
    exact hc.visits
  · intro r hm
    rcases List.mem_append.mp hm with hd|hx
    · exact hc.records r hd
    · exact (he r hx).1
  · intro x hx
    rw [b] at hx
    exact hc.boxes x hx
  · intro r hm
    rcases List.mem_append.mp hm with hd|hx
    · exact hr.records r hd
    · exact (he r hx).mono hVU

theorem append_profile {D : Directory} (hd : D.ProfileWidths) (extra : List Record)
    (he : ∀ r ∈ extra, Wiring r) : (appendRows D extra).ProfileWidths := by
  intro r hr
  rcases List.mem_append.mp hr with ha | hb
  · exact hd r ha
  · exact wiring_profile (he r hb)

theorem append_format {D : Directory} {H : ℕ} (hH : 9 ≤ H)
    (hd : ∀ r ∈ D.records, (Packet.record r).length ≤ H) (extra : List Record)
    (he : ∀ r ∈ extra, Wiring r) : ∀ r ∈ (appendRows D extra).records, (Packet.record r).length ≤ H := by
  intro r hr
  rcases List.mem_append.mp hr with ha | hb
  · exact hd r ha
  · exact (wiring_words (he r hb)).trans hH

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
