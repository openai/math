import OAI.Hierarchy.ProbeStripSizeAge
import OAI.Hierarchy.ProbeCatalystCashEntry

namespace OAI
/-! # Deriving the stock address bound from the installed seed pass -/

namespace Hierarchy.ProtocolRAM.CatalystArchive
open Computability.VPVNP.BurstRAM PrivateRAM Calendar StockCommit PurchaseStage
open scoped Fin.CommRing Classical

/-- Readiness of the actual reported commit includes the destination end of
its first stock-copy pass, including the case of zero commodities. -/
theorem priced_bank_fit {w q d : ℕ} (C : Chart w q d) (a : Attempt) (m : Memory w)
    (g : Area) (src : Sources) (labels : LabelSource) (b : Batch q d)
    (ready : Calendar.ready C (.attempt a) m) (installed : C.commit a=pricedSegment g src labels w b) :
    g.start+g.goods < 2^w := by
  have next := ready.2.2.2.2.2.2.2.2.2.2.1
  rw [installed] at next
  exact next.2.1.2

/-- Install the actual row, copy and selector bounds on the native format. -/
theorem StripSizes.Room.of_scalars {z d k q n D c e E maximum cap w start : ℕ}
    (raw : Format z d k q n) (slots : Fin n→Option Expr) (bounds : ScalarRoom D q c E cap w)
    (ports : n≤D) (codes : e≤E) (metadata : maximum≤cap)
    (copies : raw.histMass=c) (width : raw.batch.batch.maxWidth=cap)
    (bank : (PortPadding.format D start slots raw).pricedArea.start+raw.coordinates<2^w) :
    StripSizes.Room raw slots start D e maximum w := by
  refine ⟨ports,bounds.portFit,bounds.termFit,?_,?_,?_,?_,?_,?_,bank⟩
  · simpa only [copies] using bounds.copyFit
  · simpa only [copies] using bounds.sumFit
  · exact (Nat.add_le_add_left codes 1).trans bounds.codeFit
  · simpa only [width] using metadata
  · simpa only [width] using bounds.fieldFit
  · simpa only [width,copies] using bounds.wide

end Hierarchy.ProtocolRAM.CatalystArchive

end OAI
