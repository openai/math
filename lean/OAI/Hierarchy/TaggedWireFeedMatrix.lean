import OAI.Hierarchy.TaggedWireFeedAction
import OAI.Hierarchy.TaggedWireReportMatrix
import OAI.Hierarchy.ProtocolRAMCalendarFeedRead
import OAI.Hierarchy.ProtocolRAMCalendarHeldStock

namespace OAI
/-! # Ordinary tensor transfer at the native outer/inner cap boundary -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAM Calendar FeedLayout AdaptiveProbe WireTelescope Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing

variable {h d k W q D K edges r : ℕ} {F : Type*} [Field F]
variable (L : FeedLayout h (Stages h d) k) (C : Chart W q D)

private def read (addr : ℕ) (m : Memory W) (i : Data h d k) := (m (addr+PurchaseInventory.slot i)).val

/-- Both updated banks are the actual native output words. The input bank
holds the undelivered original payload for the particular physical record. -/
def outer (p : ℕ) (m : Memory W) (placed : C.columns (.outer p)=L.columns)
    (low : L.Before C.mesh C.modeAt (.outer p)) (fits : L.stop<2^W) (capFits : L.cap*L.width<2^W)
    (rows : 2^h≤2^W) (room : ∀i : Data h d k,PurchaseInventory.stock L.active m i+
      (if p<C.mesh.inject then slice C.mesh.inject L.width p*payloadUnit i else 0)<2^W) : Transfer h d k where
  old i := held C.mesh.inject L.width p*payloadUnit i
  active := PurchaseInventory.stock L.active m
  held i := held C.mesh.inject L.width (p+1)*payloadUnit i
  kept := read L.kept (after C (.feed (.outer p)) m)
  spill := read L.overflow (after C (.feed (.outer p)) m)
  balanced i := L.outer_balance C p m i (L.outer_rows C p m placed low fits capFits rows i (room i))

private def pending (p a j : ℕ) (m : Memory W) (i : Data h d k) :=
  if m (C.modeAt (.outer p a))=3 then held C.mesh.reserveSteps (PurchaseInventory.stock L.saved m i) j else 0

/-- The archived parent-purchase mode gates the still-held reserve. Its
contribution to the tensor is zero throughout an unpurchased inner run. -/
def inner (p a j : ℕ) (m fixture : Memory W) (placed : C.columns (.inner p a j)=L.columns)
    (low : L.Before C.mesh C.modeAt (.inner p a j))
    (fits : L.stop<2^W) (capFits : L.cap*L.width<2^W) (rows : 2^h≤2^W) (index : j<C.mesh.reserveSteps)
    (digit : ∀i : Data h d k,PurchaseInventory.stock L.saved m i<L.stride)
    (size : C.mesh.reserveSteps*L.stride≤L.table.size) (limit : C.mesh.reserveSteps*L.stride<2^W)
    (mounted : ∀x,L.table.base≤x→x<L.table.base+C.mesh.reserveSteps*L.stride→
      m x=feedAdvice L.table C.mesh.reserveSteps L.stride fixture x)
    (room : ∀i : Data h d k,PurchaseInventory.stock L.active m i+
      (if m (C.modeAt (.outer p a))=3 then slice C.mesh.reserveSteps (PurchaseInventory.stock L.saved m i) j else 0)<2^W) :
    Transfer h d k where
  old := pending L C p a j m
  active := PurchaseInventory.stock L.active m
  held := pending L C p a (j+1) m
  kept := read L.kept (after C (.feed (.inner p a j)) m)
  spill := read L.overflow (after C (.feed (.inner p a j)) m)
  balanced i := L.inner_balance C p a j m i index
    (L.inner_rows C p a j m fixture placed low fits capFits rows i index (digit i) size limit mounted (room i))

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer

end
end OAI
