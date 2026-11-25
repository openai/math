import OAI.Hierarchy.ProtocolRAMPurchaseShelfRecords
import OAI.Hierarchy.ProbeRetainedOrdinals
import OAI.Hierarchy.ProbeStripDirectory
import OAI.Hierarchy.ProtocolRAMPurchaseRows

namespace OAI
/-! # The native purchased candidate carrying a retained typed strip -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage
open scoped Classical Fin.CommRing

open PurchaseFrozen in
/-- A retained strip of the actual marks has one affirmative public candidate
and all of its global commodity addresses are read back from that candidate's
computed source slab. -/
theorem retainedStock {z d k : ℕ} (sh : Shelf) (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^z))) (depth : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen after : Shelf.Mem z d) (path : LiveChains S π depth (actualMarks sh phase T kind frozen (k:=k)))
    (data : ∀ key : Key z d k, ProtocolRAMPurchaseGateColumns.TileRows
      (sh.L S depth key).source (Shelf.pathRows S π depth key) after)
    (room : (depth+1)*paths z S.degree depth ≤ 2^(Native.wordBits z d Native.copies)) :
    let key := key path.1 ((PurchaseMarks.signedDirection k).symm path.2.1)
    ∃ i : PurchaseDirectory.Index (2^z) S.degree depth,
      (sh.decisions S π depth phase T kind frozen key)[i.val]'(by simpa [PurchaseFrozen.paths] using i.isLt)=true ∧
      ∀ u : ChainStrip.Axes depth k,
        (keySlot sh S depth key u).eval after (i.val:Word (Native.wordBits z d Native.copies)) =
          (PurchaseInventory.slot (stripAddress S π depth (actualMarks sh phase T kind frozen) path u) :
            Word (Native.wordBits z d Native.copies)) := by
  let marks := actualMarks sh phase T kind frozen (k:=k)
  let stratum := key path.1 ((PurchaseMarks.signedDirection k).symm path.2.1)
  have st : stage stratum=path.1 := stage_key ..
  obtain ⟨i,flag,rows⟩ := retainedRows S π depth marks path
  refine ⟨i,?_,fun u => ?_⟩
  · let bit (t : StageAt z d) :=
      (MarkTape.decisions (PurchaseTape.paths (advisedStage z d π t)
        (Fintype.equivFin (stageAt z d t).Group).toEmbedding (D:=S.degree)
        (portDigits (S.rows (stageAt z d t).span)) depth)
        ((sh.marked phase T kind frozen stratum).map Fin.castSuccEmb))[i.val]'(by
          simpa [PurchaseTape.paths] using i.isLt)
    exact (congrArg bit st).trans flag
  · have hit : (Shelf.pathRows S π depth stratum i u.1).val =
        (liveRow S π depth marks path u.1).val := by
      let tile (t : StageAt z d) := (PurchaseColumns.rowTile
        (ProtocolRAMPurchaseOwners.successor (advisedStage z d π t)
          (Fintype.equivFin (stageAt z d t).Group).toEmbedding (D:=S.degree)
          (portDigits (S.rows (stageAt z d t).span))) i u.1).val
      exact (congrArg tile st).trans (congrArg Fin.val (rows u.1))
    simpa only [stripAddress,st] using
      keySlot_tiles sh S π depth stratum after (data stratum) room i u _ hit

open PurchaseFrozen in
/-- The public quotient/remainder header locates the retained strip at a
single common RAM row for all signed coordinates of the actual batch. -/
theorem retainedBoardTiles {z d k : ℕ} (sh : Shelf) (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^z))) (depth start : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen after : Shelf.Mem z d) (path : LiveChains S π depth (actualMarks sh phase T kind frozen (k:=k)))
    (data : ∀ key : Key z d k, ProtocolRAMPurchaseGateColumns.TileRows
      (sh.L S depth key).source (Shelf.pathRows S π depth key) after)
    (loaded : (stratumHeader z d k S.degree depth start).Loaded after)
    (keys : count z d k ≤ 2^(Native.wordBits z d Native.copies))
    (room : (depth+1)*paths z S.degree depth ≤ 2^(Native.wordBits z d Native.copies)) :
    let header := stratumHeader z d k S.degree depth start
    ∃ r : Fin header.count, ∀ u : ChainStrip.Axes depth k,
      (allChainSlot (z:=z) (d:=d) sh S depth header u).eval after
        (r.val:Word (Native.wordBits z d Native.copies)) =
      (PurchaseInventory.slot (stripAddress S π depth (actualMarks sh phase T kind frozen) path u) :
        Word (Native.wordBits z d Native.copies)) := by
  let header := stratumHeader z d k S.degree depth start
  let stratum := key path.1 ((PurchaseMarks.signedDirection k).symm path.2.1)
  obtain ⟨i,_,correct⟩ := retainedStock sh S π depth phase T kind frozen after path data room
  let localRow : Fin header.ports := ⟨i.val,by
    simpa [header,stratumHeader,PurchaseFrozen.paths] using i.isLt⟩
  let r := header.enum ⟨stratum,localRow⟩
  have split := header_pair header after loaded stratum localRow
  have keyRoom : stratum.val<2^(Native.wordBits z d Native.copies) := stratum.isLt.trans_le keys
  refine ⟨r,fun u => ?_⟩
  exact (allChainSlot_read sh S depth header u after _ stratum _ keys
    (by rw [split.1,Fin.val_cast_of_lt keyRoom]) split.2).trans (correct u)

open PurchaseFrozen in
theorem retainedBoard {z d k : ℕ} (sh : Shelf) (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^z))) (depth start : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen after : Shelf.Mem z d) (path : LiveChains S π depth (actualMarks sh phase T kind frozen (k:=k)))
    (data : ∀ key : Key z d k, sh.PortData S π depth key after)
    (loaded : (stratumHeader z d k S.degree depth start).Loaded after)
    (keys : count z d k ≤ 2^(Native.wordBits z d Native.copies))
    (room : (depth+1)*paths z S.degree depth ≤ 2^(Native.wordBits z d Native.copies)) :
    let header := stratumHeader z d k S.degree depth start
    ∃ r : Fin header.count, ∀ u : ChainStrip.Axes depth k,
      (allChainSlot (z:=z) (d:=d) sh S depth header u).eval after
        (r.val:Word (Native.wordBits z d Native.copies)) =
      (PurchaseInventory.slot (stripAddress S π depth (actualMarks sh phase T kind frozen) path u) :
        Word (Native.wordBits z d Native.copies)) :=
  retainedBoardTiles sh S π depth start phase T kind frozen after path (fun key=>(data key).tiles) loaded keys room

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
