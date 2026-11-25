import OAI.Computability.BorderVNP.CubeMeanReindex
import OAI.Computability.BorderVNP.CubeLabelTraffic
import OAI.Computability.BorderVNP.CubeMeanPacked

/-! # The sparse public cable and delivery tables return the physical packing labels

The chooser reads the source and destination cell words and the width from each cable
triple. Each delivery contributes its destination and width from the seven-word row.
Slot placement may leave holes or rows for cables absorbed into one cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open MeanChoice LabelIndex Crossing Finset

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable (N : Network D P bits) (cell : N.Site → Cell)
variable {A : Type*} [Fintype A] (recv : A → Cell) (dataWidth : A → ℕ)

/-- Descriptor rows before public numbering and padding. Every live wire and
delivered datum represents its actual number of unit bits. -/
abbrev networkRows :=
  trafficRows (crossSrc N cell) (crossDst N cell) recv (crossWidth N cell) dataWidth

/-- A native label scan starts with the cache decoded from the original traffic tables. -/
def tableCodes (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) (z : ℕ) : Fin l.cells → Fin (z+1) :=
  scanNat (fromTables l m ep) (List.finRange l.cells) ∅ (fun _ => 0) (cache (fromTables l m ep) ∅ (fun _ => 0))

omit [Fintype Cell] [DecidableEq Cell] [Fintype A] in
/-- The row and column conditions on the actual input that suffice for transporting the
physical load calculation. Zero-width rows may name any valid dummy endpoints. -/
theorem placement_of_columns (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m)
    (cells : Cell ≃ Fin l.cells) (edgeOrd : N.CrossingEdge cell ↪ Fin l.cableCount) (dataOrd : A ↪ Fin l.deliveryCount)
    (hc : ∀ e, let t := cableAt l m (edgeOrd e)
      (t.src = (cells (crossSrc N cell e)).val ∧ t.dst = (cells (crossDst N cell e)).val ∧ t.width = crossWidth N cell e) ∨
      (liveWidth t = 0 ∧ crossWidth N cell e = 0))
    (ha : ∀ a, let t := deliveryAt l m (dataOrd a)
      (t.1 = (cells (recv a)).val ∧ t.2 = dataWidth a) ∨ (t.2 = 0 ∧ dataWidth a = 0))
    (ec : ∀ i ∉ Set.range edgeOrd, liveWidth (cableAt l m i) = 0)
    (dc : ∀ i ∉ Set.range dataOrd, (deliveryAt l m i).2 = 0) :
    RowPlacement (networkRows N cell recv dataWidth) (fromTables l m ep) cells (edgeOrd.sumMap dataOrd) := by
  constructor
  · rintro (e|a)
    · let t := cableAt l m (edgeOrd e)
      rcases hc e with ⟨hs,hd,hw⟩ | hz
      · left
        have hdiff : t.src ≠ t.dst := by
          intro h
          exact e.property (cells.injective (Fin.ext (hs.symm.trans (h.trans hd))))
        change Traffic.cable ⟨t.src,_⟩ ⟨t.dst,_⟩ (liveWidth t) =
          Traffic.cable (cells (crossSrc N cell e)) (cells (crossDst N cell e)) (crossWidth N cell e)
        rw [liveWidth,ite_eq_right hdiff,hw]
        exact congrArg₂ (fun a b => Traffic.cable a b (crossWidth N cell e)) (Fin.ext hs) (Fin.ext hd)
      · exact Or.inr hz
    · rcases ha a with ⟨hr,hw⟩ | hz
      · left
        change Traffic.delivery ⟨(deliveryAt l m (dataOrd a)).1,_⟩ (deliveryAt l m (dataOrd a)).2 =
          Traffic.delivery (cells (recv a)) (dataWidth a)
        exact congrArg₂ Traffic.delivery (Fin.ext hr) hw
      · exact Or.inr hz
  · rintro (i|j) h
    · exact ec i (fun ⟨e,he⟩ => h ⟨.inl e,congrArg Sum.inl he⟩)
    · exact dc j (fun ⟨a,ha⟩ => h ⟨.inr a,congrArg Sum.inr ha⟩)

/-- Visiting the actual cells in increasing public ordinal order yields their original
physical packing codes, including sparse arrays and absorbed edges. -/
theorem tableCodes_eq_meanPackedCodes (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m)
    (cells : Cell ≃ Fin l.cells) {edgeOrd : N.CrossingEdge cell ↪ Fin l.cableCount} {dataOrd : A ↪ Fin l.deliveryCount}
    (p : RowPlacement (networkRows N cell recv dataWidth) (fromTables l m ep) cells (edgeOrd.sumMap dataOrd)) (z : ℕ) :
    tableCodes l m ep z = meanPackedCodes N cell recv dataWidth ((List.finRange l.cells).map cells.symm) z ∘ cells.symm := by
  let cs := (List.finRange l.cells).map cells.symm
  have order : cs.map cells = List.finRange l.cells := by simp [cs,List.map_map,Function.comp_def]
  have h := p.scan cs ∅ (fun _ => (0 : Fin (z+1)))
  rw [order,map_empty] at h
  have hf := scanNat_eq_follow (crossSrc N cell) (crossDst N cell) recv (crossWidth N cell) dataWidth
    (fun e => e.property) cs ∅ (fun _ => (0 : Fin (z+1)))
  change tableCodes l m ep z = (scanNat (networkRows N cell recv dataWidth) cs ∅ (fun _ => 0)
    (cache (networkRows N cell recv dataWidth) ∅ (fun _ => 0))) ∘ cells.symm at h
  rw [hf] at h
  exact h

/-- Decoding an output symbol from the physical arrays produces the same product label
used for the directed packet bins. -/
theorem decoded_tableCodes (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m)
    (cells : Cell ≃ Fin l.cells) {edgeOrd : N.CrossingEdge cell ↪ Fin l.cableCount} {dataOrd : A ↪ Fin l.deliveryCount}
    (p : RowPlacement (networkRows N cell recv dataWidth) (fromTables l m ep) cells (edgeOrd.sumMap dataOrd))
    (n d : ℕ) (hd : 0 < d) (c : Cell) :
    decodeProduct n d hd (tableCodes l m ep (d^(n+1)-1) (cells c)) =
      meanPackedLabel N cell recv dataWidth ((List.finRange l.cells).map cells.symm) n d hd c := by
  rw [tableCodes_eq_meanPackedCodes N cell recv dataWidth l m ep cells p]
  simp [meanPackedLabel]

/-- The two simultaneous load bounds for the labels decoded directly from the original public
arrays, with zero slots and ascending public cell order. -/
theorem tableCodes_balanced (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m)
    (cells : Cell ≃ Fin l.cells) {edgeOrd : N.CrossingEdge cell ↪ Fin l.cableCount} {dataOrd : A ↪ Fin l.deliveryCount}
    (p : RowPlacement (networkRows N cell recv dataWidth) (fromTables l m ep) cells (edgeOrd.sumMap dataOrd))
    (n d : ℕ) (hd : 0 < d) {W : ℝ} {M : ℕ} (h : PackedLabelBudget N cell recv dataWidth W M (d^(n+1))) :
    let label := fun c => decodeProduct n d hd (tableCodes l m ep (d^(n+1)-1) (cells c))
    (∀ u v, Balancing.load (Balancing.cable (fun b : LiveBit N cell => crossSrc N cell b.1)
      (fun b : LiveBit N cell => crossDst N cell b.1) u v) label ≤ 4*W/(d^(n+1) : ℕ)^2) ∧
    ∀ u, Balancing.load (Balancing.datum (fun b : Balancing.Bits dataWidth => recv b.1) u) label ≤ 4*W/(d^(n+1) : ℕ) := by
  intro label
  let cs := (List.finRange l.cells).map cells.symm
  have eq : label = meanPackedLabel N cell recv dataWidth cs n d hd :=
    funext (decoded_tableCodes N cell recv dataWidth l m ep cells p n d hd)
  have hd' : cs.Nodup := List.Nodup.map cells.symm.injective (List.nodup_finRange l.cells)
  have hc' : cs.toFinset = univ := by
    ext c
    simp [cs,List.mem_map]
    exact cells.symm.surjective c
  rw [eq]
  exact meanPackedLoads N cell recv dataWidth cs hd' hc' n d hd h

end Cube.Physical

end BorderVNP
end Computability
end OAI
