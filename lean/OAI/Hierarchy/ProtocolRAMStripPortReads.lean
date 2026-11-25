import OAI.Hierarchy.ProtocolRAMStripColumnPrograms
import OAI.Hierarchy.ProtocolRAMStripNativeIDs

namespace OAI
/-! # Actual CT and original chronological operands of each strip port -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe BoughtSockets PurchaseFrozen
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
variable {z W k attempts K H w : ℕ}

theorem purchased_column (b : Board) (v : Directory attempts) (S : PurchaseSampler) (catalogue columnBase : ℕ)
    (π : Equiv.Perm (Fin (2^z))) (depth : ℕ) (marks : ReportSockets.Marks z W k attempts) (a : Fin attempts)
    (p : LiveChains S π depth (marks a)) (groups : Fin K≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k attempts)) H)
    (m : Shelf.Mem z (2^W)) (c : ChainStrip.Columns depth)
    (reports : ColumnROM.Tables z W k attempts columnBase v.remapBase v.sitesBase v.superBase groups packed π m)
    (outer : (v.header z (2^W) k S.degree depth).Loaded m)
    (keys : (StripDirectory.stratumHeader z (2^W) k S.degree depth v.keysBase).Loaded m)
    (data : (v.shelf a).PortData S π depth (pathKey S π depth marks a p) m)
    (rooms : let w:=Native.wordBits z (2^W) Native.copies
      attempts≤2^w ∧ count z (2^W) k≤2^w ∧ (depth+1)*paths z S.degree depth≤2^w) :
    let ports:=purchasePorts b v (v.shelf a) S catalogue columnBase v.keysBase K packed.groups H z W k depth a.val
    (ports.column c).eval m ((BoughtLocation.relative p).val:Word _)=
      (ColumnROM.number (.inr (.inl (stripPlace S π depth (marks a) p c))):Word _) := by
  let head:=v.header z (2^W) k S.degree depth
  let pos:=chainPosition depth c
  let side:=decide (c.val.val%2=1)
  let row:=eventIndex v.keysBase S π depth marks a p (BoughtLocation.localIndex p)
  have index : row=BoughtLocation.relative p := rfl
  have exactLookup:=v.retained_position columnBase S π depth marks a p groups packed m (BoughtLocation.localIndex p)
    pos side reports outer keys data rooms (BoughtLocation.rows p)
  have direct:=v.atPosition_event columnBase S z W k depth K packed.groups H pos side m a row outer rooms.1
  have chosen := chain_chosenColumn S π depth (marks a) p c
  have numbered := congrArg
    (fun x : CoreBoard.Columns z (2^W) =>
      (ColumnROM.number x : Word (Native.wordBits z (2^W) Native.copies))) chosen
  exact direct.symm.trans (exactLookup.trans numbered)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
