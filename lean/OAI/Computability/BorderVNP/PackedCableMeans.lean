import OAI.Computability.BorderVNP.PackedCableColumns

/-! # Packing labels computed from the produced native arrays

The router's complete traffic array consists of one original edge ordinal per
sparse cable and exactly the positive delivery intervals. Native publication
preserves the geometry words. Hence the chooser on the resulting memory uses
the directed cable and data loads of the actual final network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CableTriples

open Crossing BorderVNP.Cube Cube.Physical Cube.LabelIndex CellAddressCircuit CellAddressPhysical
open ParseBatchSort RoutingISA VPVNP.BurstRAM DiagonalResidueRAM Function

variable {D s n d k w b W : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (l : LabelIndex.Layout) (cell : N.Site → Fin l.cells) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin l.cableCount) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s l.cableCount n l.cells d k w σ) {x : σ → Bool}

/-- For the real geometry and compact directory outputs, the native sparse arrays
supply legal endpoints and the exact row placement for the physical chooser. -/
theorem published_placement (hk : k ≤ b) (hw : w ≤ b) (wordFit : b ≤ W)
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (cells : 0 < l.cells) (mz : Memory W) (head : ℕ)
    (geom : ∀ i : Fin (l.cableCount*3), mz (l.cables+i.val) = word W (value fun j => (frame F hk hw).eval x (i,j)))
    (dir : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (bound : dir.DestinationBounds)
    (legal : ∀ key, (dir.keyPlacement pp lp key).1 < l.cells) (count : (dir.directory pp lp).length = l.deliveryCount)
    (header : head+9 < l.cables) (before : head+9 < l.deliveries)
    (separate : l.cables+l.cableCount*3 ≤ l.deliveries ∨ l.deliveries+7*l.deliveryCount ≤ l.cables)
    (fits : ∀ i : Fin (dir.directory pp lp).length, ∀ a ∈ (dir.directory pp lp)[i.val].words, a < 2^W) :
    let rows := dir.directory pp lp
    let mem := readings (Directory.ISA.publish mz head l.deliveries rows)
    let recv (i : Fin rows.length) := (⟨rows[i.val].cell,delivery_cell_lt dir pp lp bound legal i⟩ : Fin l.cells)
    let size (i : Fin rows.length) := rows[i.val].width
    ∃ ep : Endpoints l mem,
      MeanChoice.RowPlacement (networkRows N cell recv size) (fromTables l mem ep) (Equiv.refl _)
        ((wireOrd N cell edgeID).sumMap (finCongr count).toEmbedding) := by
  intro rows mem recv size
  have hc (i : Fin l.cableCount) : cableAt l mem i = row F x i :=
    (cableAt_publish mz head l rows header (by simpa only [rows,count] using separate) i).trans
      (cableAt_outputs F hk hw wordFit x l mz geom i)
  have hd (i : Fin rows.length) : deliveryAt l mem i = (rows[i.val].cell,rows[i.val].width) :=
    deliveryAt_publish mz head l rows before i (fits i)
  have ep : Endpoints l mem := by
    constructor
    · intro i hi
      rw [hc ⟨i,hi⟩]
      exact row_endpoints N cell aux siteID edgeID portID F net code cells _
    · intro i hi
      let j : Fin rows.length := ⟨i,by simpa only [rows,count] using hi⟩
      rw [hd j]
      exact delivery_cell_lt dir pp lp bound legal j
  refine ⟨ep,placement_of_columns N cell recv size l mem ep (Equiv.refl _) (wireOrd N cell edgeID)
    (finCongr count).toEmbedding ?_ ?_ ?_ ?_⟩
  · intro e
    dsimp only
    rw [hc,row_crossing N cell aux siteID edgeID portID F net code]
    split
    · exact Or.inr ⟨rfl,by assumption⟩
    · exact Or.inl ⟨rfl,rfl,rfl⟩
  · intro i
    exact Or.inl ⟨congrArg Prod.fst (hd i),congrArg Prod.snd (hd i)⟩
  · intro i hi
    rw [hc,row_unused N cell aux siteID edgeID portID F net code i hi]
    rfl
  · intro i hi
    exact (hi ((finCongr count).surjective i)).elim

end Packing.CableTriples

end BorderVNP
end Computability
end OAI
