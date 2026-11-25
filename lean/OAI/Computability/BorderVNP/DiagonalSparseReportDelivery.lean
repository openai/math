import OAI.Computability.BorderVNP.CellPacketGeometryOriginalDelivery
import OAI.Computability.BorderVNP.CellTeamLiveDelivery
import OAI.Computability.BorderVNP.CellPacketTypedInitializer

/-! # Paying for the actual opaque and report-bundle rows in the signed input clock -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.Layout

/-- The original ordinal and the attained receiver of every opaque box in a real
cell of the published geometry. -/
structure OriginalBoxRows {C : ℕ} (d : Packing.Directory.Layout) (pp : ℕ → ℕ × ℕ)
    (places : Fin C → RoutingISA.CellPacket.Placed (Fin d.entries)) where
  /-- Distinct placed boxes are distinct originally transmitted inputs. -/
  entry : ((c : Fin C) × Fin ((places c).boxes.filterMap Sum.getRight?).length) ↪ Fin d.entries
  /-- The original directory entry was sent to this box's actual cell. -/
  received : ∀ z, (pp (entry z).val).1=z.1.val

end Packing.Directory.Layout

namespace CellPacketGeometry.History

open CellSparse Packet Packing.Inherited FrozenTape SiteWords LiveWords Packing.Directory Cube.TeamRowClock RoutingISA
open scoped Classical

variable {a C cap d t : ℕ} {R B U V E A : Type} (dir : Packing.Directory.Layout)
    (pp lp : ℕ → ℕ × ℕ) (recv : A → Fin (C+1)) (width : A → ℕ)
    (located : RowLocations (dir.directory pp lp) Fin.val recv width)
    (tail : 0<dir.literal/2) (short : dir.description≤dir.literal/2)
    (S : Schema R B) (L : Schema U V) (entry : Fin dir.entries ↪ Fin a) (known : Fin a → List (List Factor))
    (sh : ∀ i, (S.tags i).length≤cap) (lh : ∀ i, (L.tags i).length≤cap)
    (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (arg : E → ℕ)
    (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)

local notation3 (prettyPrint := false) "G" => directory S L (originalBoxes entry known) sh lh priv rep arg x y cells off box

set_option maxHeartbeats 900000 in
/-- Each opaque source occurrence on the complete physical cell array uses
its unique transmitted entry. Surjectivity of the real-cell enumeration
ensures that the spare cell cannot introduce an additional opaque source. -/
noncomputable def placedBoxBitDelivery (places : Fin (C+1) → CellPacket.Placed (Fin dir.entries))
    (shape : ∀ c, (places c).boxes=(G).cellBoxes c) (whereSent : ∀ j, (pp j.val).1=(cells (entry j)).val) :
    BitDelivery (fun z : (c : Fin (C+1)) × Fin ((places c).boxes.filterMap Sum.getRight?).length => z.1)
      (fun _ => dir.description) recv width := by
  let occ := (G).deliveryEmbedding (original_once S L entry known sh lh priv rep arg x y cells off box)
  let ordinal (c : Fin (C+1)) : Fin ((places c).boxes.filterMap Sum.getRight?).length ≃
      Fin (((G).cellBoxes c).filterMap Sum.getRight?).length := finCongr (by rw [shape c])
  let convert := Equiv.sigmaCongrRight ordinal
  let original := originalDelivery S L entry known sh lh priv rep arg x y cells off box
  apply dir.privateBitDelivery pp lp _ (convert.toEmbedding.trans occ) Fin.valEmbedding recv width located _ tail short
  intro z
  obtain ⟨j,hj⟩ := originalDelivery_surjective S L entry known sh lh priv rep arg x y cells off box (occ (convert z))
  have same : (⟨j.1.castSucc,j.2⟩ : (c : Fin (C+1)) × Fin (((G).cellBoxes c).filterMap Sum.getRight?).length) =
      convert z := occ.injective hj
  have cell : j.1.val=z.1.val := congrArg (fun q => q.1.val) same
  have answer := originalDelivery_receiver S L entry known sh lh priv rep arg x y cells off box j
  exact (whereSent _).trans ((congrArg (fun u => (cells (entry u)).val) hj.symm).trans ((congrArg Fin.val answer).trans cell))

/-- Recover the precise original transmission ordinal and its attained receiver
for every placed opaque site visited by the real-cell scanner. -/
noncomputable def originalPlacedRows (places : Fin C → CellPacket.Placed (Fin dir.entries))
    (shape : ∀ c, (places c).boxes=(G).cellBoxes c.castSucc)
    (whereSent : ∀ j, (pp j.val).1=(cells (entry j)).val) : dir.OriginalBoxRows pp places := by
  let ordinal (c : Fin C) : Fin ((places c).boxes.filterMap Sum.getRight?).length ≃
      Fin (((G).cellBoxes c.castSucc).filterMap Sum.getRight?).length := finCongr (by rw [shape c])
  let convert := Equiv.sigmaCongrRight ordinal
  let original := originalDelivery S L entry known sh lh priv rep arg x y cells off box
  refine ⟨convert.toEmbedding.trans original,fun z => ?_⟩
  exact (whereSent _).trans (congrArg Fin.val (originalDelivery_receiver S L entry known sh lh priv rep arg x y cells off box (convert z)))

/-- Each hidden box of a real cell occupies the corresponding installed native
private row. The terminal sorter's spare cell has no processor visit. -/
noncomputable def realPlacedBoxBitDelivery (realRecv : A → Fin C)
    (locations : RowLocations (dir.directory pp lp) Fin.val realRecv width)
    (places : Fin C → CellPacket.Placed (Fin dir.entries))
    (shape : ∀ c, (places c).boxes=(G).cellBoxes c.castSucc)
    (whereSent : ∀ j, (pp j.val).1=(cells (entry j)).val) :
    BitDelivery (fun z : (c : Fin C) × Fin ((places c).boxes.filterMap Sum.getRight?).length => z.1)
      (fun _ => dir.description) realRecv width := by
  let r := originalPlacedRows dir pp S L entry known sh lh priv rep arg x y cells off box places shape whereSent
  exact dir.privateBitDelivery pp lp _ r.entry Fin.valEmbedding realRecv width locations r.received tail short

end CellPacketGeometry.History

namespace Packing.Directory

open Cube.TeamRowClock Packing.BundleDirectory

/-- Each guessed report row preserves the source-bundle count of its cell.
Its sampled digits can vary while the actual original-entry and byte map
continue to give the delivery charge. -/
noncomputable def Layout.reportBitDelivery {C N : ℕ} {A : Type} (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (home : Fin N → Fin C) (count : Fin C → ℕ)
    (grouped : ∀ c, count c=(sourceRows home c.val).length)
    (entry : Fin N ↪ Fin d.entries) (placed : ∀ j, (pp (entry j)).1=(home j).val)
    (recv : A → Fin C) (width : A → ℕ) (rows : RowLocations (d.directory pp lp) Fin.val recv width)
    (tail : 0<d.literal/2) (short : d.description≤d.literal/2) :
    BitDelivery (fun j : (c : Fin C) × Fin (count c) => j.1) (fun _ => d.description) recv width := by
  let ungroup := (Equiv.sigmaCongrRight fun c => finCongr (grouped c)).trans (sourceEquiv home)
  apply d.privateBitDelivery pp lp _ (ungroup.toEmbedding.trans entry) Fin.valEmbedding recv width rows _ tail short
  intro j
  change (pp (entry (ungroup j))).1=j.1.val
  rw [placed]
  exact mem_sourceRows.mp (List.get_mem (sourceRows home j.1.val) (finCongr (grouped j.1) j.2))

end Packing.Directory

end BorderVNP
end Computability
end OAI
