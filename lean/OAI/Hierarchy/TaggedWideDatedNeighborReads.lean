import OAI.Hierarchy.TaggedWideDatedAddresses
import OAI.Hierarchy.TaggedWideDatedRoleSheets
import OAI.Hierarchy.TaggedWirePacketNeighborMetadata

namespace OAI
/-! # Read the two actual replay pages that serve the selected local installation gate -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor AdaptiveProbe ReportSockets
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
open WireTelescope Tagged PassiveWindow Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
variable {h W k attempts N native cap : ℕ} (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark)
    (rows : Fin N≃Source S π depth mark)
theorem neighbors (n start bits : ℕ) (s : Fin (siteLast h (2^W) k+1)) (qty id : Fin N→ℕ) (bounded : ∀i,qty i≤cap)
    {total : Widths (siteLast h (2^W) k+1)} (shape : installedWidths (sorted S π depth mark ∘ rows) qty=total) (m : Memory native)
    (published : ∀f,roleFact n S π depth mark unique rows start qty id m f)
    (siteTable : Bank) (here : Expr) (reg : Word native) (one : 1<2^native) (wide : ∀i,qty i<2^native)
    (wordRoom : (siteLast h (2^W) k+1)*stride k S.degree attempts≤2^native) (bankRoom : (siteLast h (2^W) k+1)*stride k S.degree attempts≤2^bits)
    (atSite : siteTable.read m (here.eval m reg)=((s.val*stride k S.degree attempts:ℕ):Word native)) :
    PacketTurns.NeighborReads m reg (carried (sorted S π depth mark ∘ rows) qty s bounded
        (PacketNeighbor.localSlot (sorted S π depth mark ∘ rows) qty (named S π depth mark unique rows)
          (shelfSlot S) (named_coordinate S π depth mark unique rows) s) shape)
      (pageRead (bank n start ((siteLast h (2^W) k+1)*stride k S.degree attempts) bits 0) siteTable here) (pageRead (bank n start ((siteLast h (2^W) k+1)*stride k S.degree attempts) bits 2) siteTable here) := by
  exact metadata_neighbors S π depth mark unique rows qty s bounded shape _ _ siteTable here m reg one wide
    wordRoom bankRoom bankRoom atSite (published 0) (published 2)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets

end
end OAI
