import OAI.Computability.BorderVNP.CellPacketGeometryHistoryCells
import OAI.Computability.BorderVNP.CellPacketGeometryFinalDirectory
import OAI.Computability.BorderVNP.PackedFrozenTapeSections

/-! # The real cell's stored history and final incidence rows identify its complete directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open Crossing Shortening CellSparse Packet Packing Packing.Inherited FrozenTape LiveWords SiteWords
open private actual_table from OAI.Computability.BorderVNP.CellPacketGeometryFinalDirectory

variable {a C cap d t : ℕ} {R B U V E Orig A : Type}

private theorem inactive (S : Schema R B) (x : Pins R B d → Bool) (siteID : A ↪ Fin a)
    (allOwners : ∀ r ∈ S.rows, x (.inl (r,.inl ())) = true → ∃ v, owner x r = (siteID v).val)
    (j : Fin a) (absent : j ∉ Set.range siteID) : S.selected x j.val = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro r hr active
  obtain ⟨live,key⟩ := Bool.and_eq_true_iff.mp active
  obtain ⟨v,hit⟩ := allOwners r hr live
  exact absent ⟨v,Fin.ext (hit.symm.trans (of_decide_eq_true key))⟩

variable (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
variable (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
local notation3 "G₀" => directory S L boxes sh lh priv rep args x y cells off box

variable {D n p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin a) (edgeID : N.Edge ↪ Fin n) (portID : P ↪ Fin p)
variable (state : N.Site → Site)

/-- The native sparse initializer's site-major directory is exactly the
mathematical network directory on every genuine cell. The two actual frozen
tapes provide all records, including empty blocks on unused sparse IDs. -/
theorem placed_directory (c : Fin C) (H : ℕ) (slot : Orig → ℕ) (fs : Orig → List Factor)
    (pub desc ext scratch burst : ℕ) (external : List Bool)
    (historical : S.Image x (siteID.trans Fin.valEmbedding) state)
    (final : L.Section y (siteID.trans Fin.valEmbedding) (FinalCell.binding N cell siteID edgeID portID state))
    (table : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots siteID (fun v => (state v).boxes) i)
    (bitBase : ∀ v, off (siteID v)=CellAddresses.siteBase N cell (cell v) siteID (fun z => (state z).size) ⟨v,rfl⟩)
    (boxBase : ∀ v, box (siteID v)=FinalCell.firstBox siteID (fun j => (cells j).val) state v) :
    ((G₀).placed c.castSucc H slot fs pub desc ext scratch burst external).directory =
      FinalCell.directory (fun i => (cells i).val) N cell siteID edgeID portID state c.val ((G₀).reports c.castSucc) := by
  let G := G₀
  let target := FinalCell.directory (fun i => (cells i).val) N cell siteID edgeID portID state c.val (G.reports c.castSucc)
  have bx : (G.cellBoxes c.castSucc).map (Source.factors fs) = target.boxes := by
    rw [FinalCell.directory_boxes,cell_boxes,List.map_flatMap]
    exact actual_table cells c _ _ fun i _ => table i
  have rs : G.cellRecords c.castSucc = target.records := by
    rw [FinalCell.directory_rows,cell_rows]
    apply actual_table
    intro i _
    cases key : Function.partialInv siteID i with
    | none =>
      have absent : i ∉ Set.range siteID := by
        rintro ⟨v,rfl⟩
        rw [Function.partialInv_left siteID.injective] at key
        contradiction
      rw [rows_at_anchor,inactive S x siteID historical.owners i absent,inactive L y siteID final.owners i absent]
      simp [FinalCell.slots,key]
    | some v =>
      have eqn : siteID v=i := (siteID.injective.isPartialInv v i).mp key
      subst i
      rw [rows_at_image S L boxes sh lh priv rep args x y cells off box siteID state _ historical final.atSite v]
      simp [FinalCell.slots,key,bitBase,boxBase]
  change CellSparse.Directory.mk ((G.cellBoxes c.castSucc).map (Source.factors fs)) (G.cellRecords c.castSucc)
    (G.reports c.castSucc) = target
  rw [bx,rs]
  rfl

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
