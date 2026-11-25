import OAI.Hierarchy.TaggedWireFundedTurnInputs
import OAI.Hierarchy.ProbeFixedWidePrefixRoom
import OAI.Hierarchy.ProbeFixedWidePrefixProgram

namespace OAI
/-! # Settled original counters after terminal reporting and prefix replay -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "sheet" => v.wideSignedPage h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

attribute [local irreducible] PaidWidths.output ReserveUse.output CoreRoute.stages

set_option maxHeartbeats 3000000 in
/-- The terminal reporter and both replay passes preserve each original
reserved/used cell even when many chronological withdrawals use the same key. -/
theorem wide_turn_counters {entries : ℕ} (owner : Fin entries→Fin num) (dur : Fin entries→ℕ)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    (route : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (used : Fin num→ℕ) (m : Memory w) :
    let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    let closed:=ReserveUse.output original old supply owner dur archive
    let out:=(sink).output closed route ci cj
    (∀x,x<full→m x=out x) →
    (∀j : Fin num,RouteSettlement.actual (old).used closed j.val=used j ∧
      RouteSettlement.actual (old).reserved closed j.val=supply) →
    ∀j : Fin num,RouteSettlement.actual (old).used m j.val=used j ∧
      RouteSettlement.actual (old).reserved m j.val=supply := by
  intro archive closed out keep values j
  have after : 28*2^page≤full:=v.wide_prefix_starts h width ss
  have room : rows≤2^page := by
    have bound : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<2^page:=Nat.lt_log2_self
    unfold TerminalLayout.footprint at bound
    omega
  have remembered (x : ℕ) (early : 6*2^page≤x) (late : x<8*2^page) : m x=closed x := by
    have suffix : out x=closed x:=by
      exact ProtocolRAM.sink_prefix sink closed route ci cj x
        (.inr (by change 1*2^page+rows≤x;omega)) (by change x<9*2^page;omega)
        (by change x<10*2^page;omega) (by change x<18*2^page;omega)
    exact (keep x (by omega)).trans suffix
  let off:=(j.val:Word w).val%2^page
  have lo : off<2^page:=Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨u,v₀⟩:=values j
  change (m (7*2^page+off)).val=_ ∧ (m (6*2^page+off)).val=_
  rw [remembered (7*2^page+off) (by omega) (by omega),remembered (6*2^page+off) (by omega) (by omega)]
  exact ⟨u,v₀⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
