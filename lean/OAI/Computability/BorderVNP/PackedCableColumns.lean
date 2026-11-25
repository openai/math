import OAI.Computability.BorderVNP.PackedCablePhysical
import OAI.Computability.BorderVNP.GeometryOutputPrefix
import OAI.Computability.BorderVNP.TransmissionDataColumns

/-! # Native public cable and delivery columns

Geometry emits three consecutive words per sparse cable. The subsequent
compacting writer installs seven consecutive words per nonempty delivery.
The cable array survives the disjoint delivery stores.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CableTriples

open Cube.LabelIndex CellAddressCircuit ParseBatchSort RoutingISA VPVNP.BurstRAM DiagonalResidueRAM

variable {s m n C d k w b W : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

/-- Decoding the native geometry outputs yields the same triple as the endpoint lookup. -/
theorem cableAt_outputs (hk : k ≤ b) (hw : w ≤ b) (outFit : b ≤ W) (x : σ → Bool)
    (l : Cube.LabelIndex.Layout) (mz : Memory W)
    (outputs : ∀ a : Fin (m*3), mz (l.cables+a.val) = word W (value fun j => (frame F hk hw).eval x (a,j)))
    (i : Fin m) : cableAt l (readings mz) i = row F x i := by
  have col (c : Fin 3) : readings mz (l.cables+i.val*3+c.val) = get (row F x i) c := by
    have raw := outputs (index i c)
    rw [index_val,frame_value] at raw
    have hfit := (value_lt (fun j => (frame F hk hw).eval x (index i c,j))).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) outFit)
    rw [frame_value] at hfit
    change (mz (l.cables+i.val*3+c.val)).val = _
    rw [← Nat.add_assoc] at raw
    exact (congrArg Fin.val raw).trans (word_val _ _ hfit)
  have a := col 0
  have b := col 1
  have c := col 2
  cases r : row F x i with
  | mk v u t =>
    rw [r] at a b c
    change Cube.LabelIndex.Cable.mk _ _ _ = _
    congr 1

/-- The complete geometry output is unchanged at an address outside the compact data writes. -/
theorem published_outside (mz : Memory W) (head base : ℕ) (rows : List Directory.Row)
    (a : ℕ) (different : a ≠ head+9) (outside : a < base ∨ base+7*rows.length ≤ a) :
    Directory.ISA.publish mz head base rows a = mz a := by
  rw [Directory.ISA.publish,Function.update_of_ne different,Directory.ISA.putWords_outside]
  simpa only [Directory.ISA.encodeRows_length] using outside

/-- Cable columns are immutable during publication of the separate delivery directory. -/
theorem cableAt_publish (mz : Memory W) (head : ℕ) (l : Cube.LabelIndex.Layout) (rows : List Directory.Row)
    (header : head+9 < l.cables)
    (separate : l.cables+l.cableCount*3 ≤ l.deliveries ∨ l.deliveries+7*rows.length ≤ l.cables)
    (i : Fin l.cableCount) :
    cableAt l (readings (Directory.ISA.publish mz head l.deliveries rows)) i = cableAt l (readings mz) i := by
  have col (j : Fin 3) : Directory.ISA.publish mz head l.deliveries rows (l.cables+i.val*3+j.val) =
      mz (l.cables+i.val*3+j.val) := by
    have := i.isLt
    have := j.isLt
    exact published_outside mz head l.deliveries rows _ (by omega) (by omega)
  change Cube.LabelIndex.Cable.mk _ _ _ = Cube.LabelIndex.Cable.mk _ _ _
  have hs := congrArg Fin.val (col 0)
  have hd := congrArg Fin.val (col 1)
  have hw := congrArg Fin.val (col 2)
  congr 1

/-- The chooser reads exactly the receiving cell and width of each nonempty delivery. -/
theorem deliveryAt_publish (mz : Memory W) (head : ℕ) (l : Cube.LabelIndex.Layout) (rows : List Directory.Row)
    (before : head+9 < l.deliveries) (i : Fin rows.length) (fits : ∀ a ∈ rows[i.val].words, a < 2^W) :
    deliveryAt l (readings (Directory.ISA.publish mz head l.deliveries rows)) i =
      (rows[i.val].cell,rows[i.val].width) :=
  congrArg (fun r : Directory.Row => (r.cell,r.width)) (Transmission.DataWriter.demandAt_published mz head l.deliveries rows before i fits)

/-- For a nonempty data row, its destination lies in the finite cell table because
a real lane recovers a private description or an original team/site key. -/
theorem delivery_cell_lt (D : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (bound : D.DestinationBounds)
    (legal : ∀ key, (D.keyPlacement pp lp key).1 < C) (i : Fin (D.directory pp lp).length) :
    (D.directory pp lp)[i.val].cell < C := by
  have pos : 0 < (D.directory pp lp)[i.val].width := ((D.mem_directory_iff pp lp _).mp
    (List.getElem_mem i.isLt)).choose_spec.2.2
  let bit : D.PopulatedBit pp lp := ⟨i,⟨0,pos⟩⟩
  let raw := D.rawBit pp lp bit
  have eq := (D.destinationKey_placement pp lp bound raw).1
  have actual := congrArg Directory.Row.cell (D.populatedRow pp lp i)
  exact (actual.trans eq) ▸ legal _

end Packing.CableTriples

end BorderVNP
end Computability
end OAI
