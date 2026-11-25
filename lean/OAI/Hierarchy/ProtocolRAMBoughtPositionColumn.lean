import OAI.Hierarchy.ProtocolRAMStageColumnRead
import OAI.Hierarchy.ProtocolRAMBoughtCatalogue

namespace OAI
/-! # Global column IDs at every scheduled position of a retained candidate -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets PurchaseFrozen
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {h W k attempts K H : ℕ}

def Directory.atPosition (v : Directory attempts) (columnBase : ℕ) (S : PurchaseSampler)
    (h W k depth K G H : ℕ) (position : Fin (depth+1)) (side : Bool) : Expr :=
  select (v.header h (2^W) k S.degree depth) (fun a=>
    select (StripDirectory.stratumHeader h (2^W) k S.degree depth v.keysBase) (fun i : Key h (2^W) k=>
      ColumnROM.stageColumn columnBase v.remapBase v.sitesBase v.superBase K G H k attempts
        (stage i) side (readTile (v.shelf a) S depth i position)))

theorem Directory.position_read (v : Directory attempts) (columnBase : ℕ) (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (ReportSockets.copies k attempts)) H)
    (m : Shelf.Mem h (2^W)) (a : Fin attempts) (i : Key h (2^W) k)
    (candidate : PurchaseDirectory.Index (2^h) S.degree depth) (j : Fin (depth+1)) (side : Bool) (tile : Fin (2^h))
    (reports : ColumnROM.Tables h W k attempts columnBase v.remapBase v.sitesBase v.superBase groups dir π m)
    (outer : (v.header h (2^W) k S.degree depth).Loaded m)
    (keys : (StripDirectory.stratumHeader h (2^W) k S.degree depth v.keysBase).Loaded m)
    (data : (v.shelf a).PortData S π depth i m)
    (rooms : let w:=Native.wordBits h (2^W) Native.copies
      attempts≤2^w ∧ count h (2^W) k≤2^w ∧ (depth+1)*paths h S.degree depth≤2^w)
    (hit : Shelf.pathRows S π depth i candidate j=tile.castSucc) :
    let head := v.header h (2^W) k S.degree depth
    let sub := StripDirectory.stratumHeader h (2^W) k S.degree depth v.keysBase
    let row := sub.enum ⟨i,⟨candidate.val,by simpa [sub,StripDirectory.stratumHeader,paths] using candidate.isLt⟩⟩
    (v.atPosition columnBase S h W k depth K dir.groups H j side).eval m ((head.enum ⟨a,row⟩).val:Word _)=
      (ColumnROM.number (ColumnROM.chosenColumn π (stage i) tile side):Word _) := by
  intro head sub row
  obtain ⟨aFit,iFit,cellFit⟩ := rooms
  let slot : Fin sub.ports := ⟨candidate.val,by simpa [sub,StripDirectory.stratumHeader,paths] using candidate.isLt⟩
  let parts := fun e (idx : Key h (2^W) k)=>ColumnROM.stageColumn columnBase v.remapBase v.sitesBase v.superBase
    K dir.groups H k attempts (stage idx) side (readTile (v.shelf e) S depth idx j)
  have lo := v.dispatch h (2^W) k S.degree depth m outer aFit a row (fun e=>select sub (parts e))
  have header := StripDirectory.header_pair sub m keys i slot
  have hi := select_read sub (parts a) m (row.val:Word _) (slot.val:Word _) i iFit
    (by rw [header.1,Fin.val_cast_of_lt (i.isLt.trans_le iFit)]) header.2
  have line := read_tile (v.shelf a) S π depth i m data cellFit candidate j
  rw [hit] at line
  exact lo.trans (hi.trans (ColumnROM.stage_read _ _ _ _ groups dir π m reports _ _ _ _ tile line))

/-- The selected owner's ID at any point of the retained chain is read from
its original DFS candidate, including its intermediate sampler ports. -/
theorem Directory.retained_position (v : Directory attempts) (columnBase : ℕ) (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (marks : Marks h W k attempts)
    (a : Fin attempts) (p : LiveChains S π depth (marks a)) (groups : Fin K≃AllGroups h (2^W))
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (ReportSockets.copies k attempts)) H)
    (m : Shelf.Mem h (2^W)) (candidate : PurchaseDirectory.Index (2^h) S.degree depth)
    (j : Fin (depth+1)) (side : Bool)
    (reports : ColumnROM.Tables h W k attempts columnBase v.remapBase v.sitesBase v.superBase groups dir π m)
    (outer : (v.header h (2^W) k S.degree depth).Loaded m)
    (keys : (StripDirectory.stratumHeader h (2^W) k S.degree depth v.keysBase).Loaded m)
    (data : (v.shelf a).PortData S π depth (pathKey S π depth marks a p) m)
    (rooms : let w:=Native.wordBits h (2^W) Native.copies
      attempts≤2^w ∧ count h (2^W) k≤2^w ∧ (depth+1)*paths h S.degree depth≤2^w)
    (hit : ∀j,Shelf.pathRows S π depth (pathKey S π depth marks a p) candidate j=(liveRow S π depth (marks a) p j).castSucc) :
    let head:=v.header h (2^W) k S.degree depth
    let row:=eventIndex v.keysBase S π depth marks a p candidate
    (v.atPosition columnBase S h W k depth K dir.groups H j side).eval m ((head.enum ⟨a,row⟩).val:Word _)=
      (ColumnROM.number (ColumnROM.chosenColumn π p.1 (liveRow S π depth (marks a) p j) side):Word _) := by
  simpa only [eventIndex,pathKey,stage_key] using v.position_read columnBase S π depth groups dir m a
    (pathKey S π depth marks a p) candidate j side _ reports outer keys data rooms (hit j)

end Hierarchy.ProtocolRAM.BoughtSockets
end

end OAI
