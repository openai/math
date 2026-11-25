import OAI.Hierarchy.ProbeFixedHistorySupported
import OAI.Hierarchy.ProbeFixedTerminalMask
import OAI.Hierarchy.ProbeFixedWideCoreOnly
import OAI.Hierarchy.ProbeFixedWideFunded

namespace OAI
/-! Genuine term, mate, tree and core support on both memories of the final native run. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
section
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tab" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "order" => wideRouteOrder h D k
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "route" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (directory).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "C" => v.wideSignedChart h width stock


local notation "b" => (P).catalogue
local notation "fmt" => v.nativeFormats P h width
local notation "H" => StripChart.header F s
local notation "dim" => max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k))
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A fmt (P).joint.initial width v.keepLimit
local notation "spills" => v.paidSpillPath P h width (routeBanks start cnt r) route order
local notation "boundary" => v.paidFeedPath P h width route lay
local notation "tree" => v.nativeTrees P h width
local notation "sink" => (b).sink r banks src tab dst owners

def WideHistorySupport (m : Memory w) (bits : ℕ) : Prop :=
  ∀ev∈events v.mesh,∀s0∈v.wideEventSlices h width bits ev,(b).Supported s0 m
end

theorem wide_history_supported :
    ∀ᶠ h : ℕ in Filter.atTop,∀ width, width≤2^h→v.keepLimit*width+1≤2^h→
      let P:=v.widePlacement h width
      let A:=v.privateArena P h width
      let stock:=v.fixedTerminalStock P h width
      let chart:=v.wideSignedChart h width stock
      let order:=wideRouteOrder h (2^v.W) k
      ∀size,A.endAddress v.mesh≤ size→∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) bits,
        let m:=v.wideSignedMidAt h width size stock v.radius π order raw
        v.WideHistorySupport h width (run chart (events v.mesh) m) bits ∧
          v.WideHistorySupport h width (v.wideSignedCheckoutAt h width size stock v.radius π order raw) bits := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [v.wide_spill_core_only,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight] with h real rows age
  intro width small budget P A stock chart order size extent π raw bits m
  have limits:=v.wide_stock_sizes h width age budget small
  have inventory:=v.wide_stock_at h width size extent v.radius π raw age budget small
  have stable (x : ℕ) (hx : x<A.first) : run chart (events v.mesh) m x=m x :=
    run_frame chart _ _ x inventory.mounted_all (fun e _=>(v.event_prefix P h width _ _ _ _ _ _ e x
      (hx.trans_le (Nat.le_add_right ..))).1)
  have finish:=v.wide_signed_checkout_below h width stock v.radius π order raw size
  have core:=real width small budget size extent π raw
  have compose (out : Memory (Native.wordBits h (2^v.W) Native.copies))
      (frame : ∀ x<A.first,out x=m x) (paths : v.CoreSpillRows h width out) : v.WideHistorySupport h width out bits :=
    v.supported_below h width size extent v.radius π order raw limits.words.addresses out frame limits.roles
      (rows width).1 bits (fun a _=>paths.1 a) (fun a _=>paths.2 a)
  exact ⟨compose _ stable core.1,compose _ (fun x hx=>finish x hx inventory.mounted_all) core.2⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
