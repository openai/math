import OAI.Hierarchy.ProbeFixedCatalystDateFrames
import OAI.Hierarchy.ProbeFixedCatalystBirth
import OAI.Hierarchy.ProbeFixedStripCounts
import OAI.Hierarchy.ProbeFixedCatalystMask

namespace OAI
/-! # The original paid outer row of the fixed calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CatalystArchive CoreBoard StripChart
open PurchaseStage RepairHistogram StripDirectory StockCommit StockBound
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "w" => wordBits z (2^v.W) copies
local notation "s" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "E" => v.publicHeader P z width
local notation "f" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "incoming" => resolvedStock v.mesh A P.joint.initial (build F s)

theorem catalyst_port_early (a : Attempt) :
    (StripChart.header F (withPorts s v.mesh P.catalogue P.routes) a).stop≤(A).first := by
  rw [←v.catalyst_header P z width a]
  exact ((E).ports.end_le 0).trans (v.catalyst_ports_le_first P z width)

variable [Nonempty (Fin k)]
local instance : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩

set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
/-- Only the observed chart and the original calendar's numeric window are needed
at the outer date. In particular its permutation, orbit labelling and packet histogram
come from the shared subdivision and the literal selector. -/
def payloadLocal (initial : Memory w) (phase trial : ℕ) (late : v.stripHeight≤z) (small : width≤2^z)
    (whole : Calendar.mounted C (events v.mesh) initial)
    (active : Event.attempt (.outer phase trial)∈events v.mesh)
    (num : 0<Fintype.card (Columns z (2^v.W))*k)
    (window : let a:=Attempt.outer phase trial
      TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)))
    (calibrated : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤z) :
    let a:=Attempt.outer phase trial
    PayloadLocal (z:=z) (W:=v.W) (k:=k) (depth:=v.depth)
      (q:=(StripChart.catalogue F (v.configured (v.seed P z width)) v.cost).alphabet)
      (J:=v.purchasePacketMenu.index) (K:=v.copyScale) (payload:=width)
      F s v.mesh P.catalogue P.routes phase trial (incoming a)
      C (entryMemory C initial a) (g a) v.finish (v.basePhase width) (PacketWidths.ofMenu v.purchasePacketMenu) := by
  dsimp only
  let a:=Attempt.outer phase trial
  let H:=StripChart.header F (withPorts s v.mesh P.catalogue P.routes) a
  have mask:=v.catalystMaskBounds_at_height P z width r banks src tab dst owners calibrated a
  have ready:=entryMemory_ready C initial a whole active
  have commit : (C).commit a=pricedSegment (f a).pricedArea (f a).stockSource (g a) w
      (enabledBatch (f a).market.layout (f a).board):=rfl
  have size:=v.payload_size_room P z width C (entryMemory C initial a) (g a) (f a).stockSource
    (enabledBatch (f a).market.layout (f a).board) phase trial (incoming a) late small ready commit
  have lo : H.stop≤(A).base v.mesh (.attempt a):=(v.catalyst_port_early P z width a).trans (Nat.le_add_right ..)
  have stopAt : (A).base v.mesh (.attempt a)≤(C).stopAt a := (v.catalyst_birth_room P z width a).1.trans (min_le_left ..)
  have stopBelow : (C).stopAt a < (repair C a).repairBits.base:=mask.mask.stop
  have all:=v.date_market_rows z P width a
  have wide:=v.date_prefix_fit z
  have copies:=v.date_copies z P width phase trial 0 0
  refine ⟨size,?_,?_,all,wide,size.portFit,⟨0,num⟩,copies.1,copies.2.1,ready,
    v.catalyst_cash_board P z width r banks src tab dst owners a window,commit,rfl,rfl,rfl,
    v.catalyst_date_mask P z width r banks src tab dst owners initial a whole active mask⟩
  · exact lo.trans (stopAt.trans (stopBelow.le.trans ((Nat.le_add_right ..).trans mask.low)))
  · exact fun x _ hx=>(v.event_prefix P z width r banks src tab dst owners (.attempt a) x (hx.trans_le lo)).1

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
