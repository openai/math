import OAI.Hierarchy.ProbeFixedCatalystUpper
import OAI.Hierarchy.ProbeFixedWideFunded
import OAI.Hierarchy.ProbeFixedWideRowBoards
import OAI.Hierarchy.ProbeFixedTerminalMask

namespace OAI
/-! Per-attempt upper invoice from the actual settled native RAM words and their
original radii. All prices are independent of word bounds on final edge loads. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
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

local notation "G" => v.stamp P h width r banks src tab dst owners
local notation "ord" => v.wideOrder h width
local notation "E" => v.publicHeader P h width
local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel

theorem wide_direct_invoice (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (π : Equiv.Perm (Fin (2^h)))
    (raw : Boot.Tape h D) (a : Attempt) (entry : Memory w) (pre post : List Event)
    (word : (A).endAddress v.mesh<2^w) (narrow : dim≤2^w)
    (room : (b).rows<2^w) (metrics : BoughtSockets.Public.maxMetric v.radius<2^w)
    (marks : Marks h v.W k jobs) (shape : jobs*(PurchaseFrozen.count h D k*PurchaseFrozen.paths h v.sampler.degree v.depth)=(b).boughtRows)
    (mounted : Calendar.mounted C (events v.mesh) (v.wideSignedMidAt h width size stock v.radius π order raw))
    (cut : Slot C (v.wideSignedMidAt h width size stock v.radius π order raw) (.attempt a) pre post entry) :
    let mid:=v.wideSignedMidAt h width size stock v.radius π order raw
    let final:=run C (events v.mesh) mid
    let len:=extendedLength ((b).ordinal v.sampler π v.depth marks ord shape) (lenCode v.sampler π v.depth marks v.radius)
    ∃mask mate,(tree a).catalystMate=some (mask,mate) ∧ ∀ i : Fin (fmt a).occurrences,
      addressPrice len ((G a).edge.eval final (i.val:Word w)).val+
        (if mask.eval final (i.val:Word w)=0 then 0 else addressPrice len (mate.eval final (i.val:Word w)).val)
        ≤v.paidRate P h width r banks src tab dst owners final a i := by
  intro mid final len
  obtain ⟨_,_,seen,econ,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock v.radius π order raw word
  have stable (x : ℕ) (hx : x<(A).first) : final x=mid x :=
    run_frame C _ _ x mounted (fun e _=>(v.event_prefix P h width r banks src tab dst owners e x
      (hx.trans_le (Nat.le_add_right ..))).1)
  have core:=(v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
  have first:(A).first<2^w:=(Nat.le_add_right ..).trans_lt word
  have snap:=seen.frame (core.trans_lt first) (fun x hx=>stable x (hx.trans_le core))
  have portLow:=((E).ports.end_le 0).trans (v.catalyst_ports_le_first P h width)
  have hdr : (H a).Loaded final:=(v.catalyst_header P h width a) ▸
    (econ.ports 0).frame (fun x _ hx=>stable x (hx.trans_le portLow))
  have codes (e : Edges v.sampler h D k) : ((b).core.lengthCode.eval final (((ord).symm e).val:Word w)).val=coreCode v.sampler v.radius e := by
    have code:=(snap.board.rows ((ord).symm e)).2.2.2.1
    rw [(ord).apply_symm_apply] at code
    exact (congrArg Fin.val code).trans (Fin.val_cast_of_lt ((BoughtSockets.Public.coreCode_le _ _ e).trans_lt metrics))
  have pos : 0<w:=by unfold Native.wordBits; omega
  obtain ⟨mask,mate,pair,classification⟩:=v.terminal_mask P h width a final narrow hdr
  refine ⟨mask,mate,pair,v.direct_invoice_le P h width r banks src tab dst owners a mid entry pre post cut len mask mate room.le ?_ ?_ ?_⟩
  · intro i off
    have sameOut : run C (events (C).mesh) mid = final :=
      congrArg (fun mesh => run C (events mesh) mid)
        (v.common_clock P h width r banks src tab dst owners)
    have zero : mask.eval final (i.val : Word w) = 0 := by
      simpa only [off, Bool.false_eq_true, ite_false] using classification i
    exact (congrArg (fun mem => mask.eval mem (i.val : Word w)) sameOut).trans zero
  · exact (b).extended_fee_le v.sampler π marks ord shape final v.radius room pos codes
  · intro i flag
    exact v.physical_catalyst_bounds P h width r banks src tab dst owners a π marks ord shape final i mask mate pair
      narrow room snap.padded hdr flag

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
