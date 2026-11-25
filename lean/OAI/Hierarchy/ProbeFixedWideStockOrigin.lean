import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProbeFixedStockOriginal
import OAI.Hierarchy.ProtocolRAMCalendarStockSliceOrigin

namespace OAI
/-! # Reserve slices and occurrence/half tables on the signed boot's actual output -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute
open CatalystArchive StripChart StockBound StockCommit StripDirectory
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "d" => 2^v.W
local notation "N" => Stages h d
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "w" => wordBits h d copies
local notation "G" => v.privateArena P h width
local notation "B" => v.nativeBoards P h width
local notation "f" => v.nativeFormats P h width
local notation "H" => v.publicHeader P h width
local notation "freq" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
local notation "digits" => v.keepLimit*width+1
local notation "tbl" => sliceROM ((P).joint.initial+PurchaseInventory.footprint h N k) v.mesh.reserveSteps digits

/-- The two public banks on the physical CT output agree pointwise with the
integer reserve-slice and half functions. Both may use this very tape as
their original fallback memory. -/
theorem wide_stock_pages (size : ℕ) (extent : (G).endAddress v.mesh ≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h d k) (raw : Boot.Tape h d)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (localRoom : slots≤2^w) (alphabet : v.menu.alphabet≤2^w)
    (copiesRoom : v.menu.copiesAt v.copyScale width<2^w)
    (mass : v.menu.alphabet*v.menu.copiesAt v.copyScale width<2^w) :
    let mem:=v.wideSignedMidAt h width size stock M π o raw
    (H).Resident mem →
    (∀x,(tbl).base≤x→x<(tbl).base+v.mesh.reserveSteps*digits→
      mem x=feedAdvice tbl v.mesh.reserveSteps digits mem x) ∧
    (∀a,Original (f a) (v.stamp P h width r banks src tab dst owners a) (StripChart.start B a) (G).first mem mem) := by
  intro mem resident
  let market:=v.catalystMarkets P h width
  let srcWords:=v.wideSignedWords h width stock M π o raw
  obtain ⟨rest,atWords⟩ : ∃rest : Boot.Tape h d,srcWords=
      JointHeader.words (P).joint h d N k freq π (fun _=>0) rest := ⟨_,rfl⟩
  have same : mem=Boot.booted market size (JointHeader.words (P).joint h d N k freq π (fun _=>0) rest) :=
    congrArg (Boot.booted market size) atWords
  have geom:=v.wideGeometryPrefix h width
  have layout:=v.catalyst_market_layout_at P h width size geom.2.1 extent
  have start : JointHeader.stop (P).joint h N k (DeadlineROM.count v.mesh)=(H).ports.base := rfl
  have before : JointHeader.stop (P).joint h N k (DeadlineROM.count v.mesh) ≤ (G).first := by
    rw [start]
    exact (Nat.le_add_right ..).trans (v.stock_port_room P h width)
  have hdrFit:=before.trans ((Nat.le_add_right .. : (G).first≤(G).endAddress v.mesh).trans extent)
  have low (i : Fin (Whole.attempts v.mesh).length) := before.trans (v.catalyst_market_low P h width i)
  have slices:=JointHeader.boot_slice («N»:=N) (P).joint freq π (fun _=>0) rest mem market layout
    Nat.one_le_two_pow geom.1 geom.2.1 hdrFit low
  have halves:=StockBound.boot_half («N»:=N) (P).joint freq π (fun _=>0) rest mem market layout
    Nat.one_le_two_pow geom.1 geom.2.1 hdrFit low
  constructor
  · intro x lo hi
    exact (congrFun same x).trans (slices x lo hi)
  · apply v.stock_original P h width r banks src tab dst owners mem mem resident _ localRoom alphabet copiesRoom mass
    intro table x lo hi
    exact (congrFun same x).trans (halves x lo hi)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
