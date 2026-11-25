import OAI.Computability.BorderVNP.CubeGroupDirectoryWords

/-! # Balanced incoming loads on the native seven-word delivery array

Sparse row placement may introduce holes and move zero-width entries to dummy
destinations. After decoding the chosen label words, every actual delivery
still contributes its exact width to the same bin as the original network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Crossing Physical MeanChoice LabelIndex Finset

variable {l : GroupWeights.Layout} {dir : LabelIndex.Layout} {before : ℕ → ℕ} {ep : Endpoints dir before}
variable {D : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable {A : Type*} [Fintype A]

/-- The grouped directory's incoming-label bound follows from the physical
packed network and the actual sparse cable and delivery row placement. -/
theorem directory_data_balanced (N : Network D P bits) (cell : N.Site → Cell)
    (recv : A → Cell) (w : A → ℕ) (cellNum : Cell ≃ Fin dir.cells)
    {edgeOrd : N.CrossingEdge cell ↪ Fin dir.cableCount} {dataOrd : A ↪ Fin dir.deliveryCount}
    (placement : RowPlacement (networkRows N cell recv w) (fromTables dir before ep)
      cellNum (edgeOrd.sumMap dataOrd)) (cells : l.cells = dir.cells)
    (n : ℕ) (hd : 0 < l.groups) {W : ℝ} {M : ℕ}
    (budget : PackedLabelBudget N cell recv w W M (l.groups^(n+1))) (u : Label (n+1) l.groups) :
    let widths := fun j : Fin dir.deliveryCount => (deliveryAt dir before j.val).2
    Balancing.load (Balancing.datum (fun j : Balancing.Bits widths => directoryRecv cells ep j.1) u)
      (directoryLabel cells hd ep n) ≤ 4*W/((l.groups^(n+1) : ℕ) : ℝ) := by
  intro widths
  let label := fun c : Cell => decodeProduct n l.groups hd
    (tableCodes dir before ep (l.groups^(n+1)-1) (cellNum c))
  have trueBound := (tableCodes_balanced N cell recv w dir before ep cellNum placement n l.groups hd budget).2 u
  have shift : (∑ a, if label (recv a) = u then (w a : ℝ) else 0) =
      ∑ j, if directoryLabel cells hd ep n (directoryRecv cells ep j) = u then (widths j : ℝ) else 0 := by
    apply Fintype.sum_of_injective dataOrd dataOrd.injective
    · intro j miss
      have unused := placement.unused (.inr j) (by
        rintro ⟨e|a,eq⟩
        · contradiction
        · exact miss ⟨a,Sum.inr.inj eq⟩)
      change widths j = 0 at unused
      simp [unused]
    · intro a
      have atRow := placement.live (.inr a)
      change rowEquivalent (.delivery ⟨(deliveryAt dir before (dataOrd a).val).1,_⟩ (widths (dataOrd a)))
        (.delivery (cellNum (recv a)) (w a)) at atRow
      rcases atRow with eq | ⟨zrow,zorig⟩
      · obtain ⟨cellEq,widthEq⟩ := Traffic.delivery.inj eq
        have he : finCongr cells (directoryRecv cells ep (dataOrd a)) = cellNum (recv a) :=
          Fin.ext (congrArg Fin.val cellEq)
        simp only [directoryLabel,he,widthEq,label]
      · change widths (dataOrd a) = 0 at zrow
        change w a = 0 at zorig
        simp [zrow,zorig]
  rw [datum_load_eq_widths (directoryLabel cells hd ep n) (directoryRecv cells ep) widths u,← shift]
  rw [← datum_load_eq_widths label recv w u]
  exact trueBound

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
