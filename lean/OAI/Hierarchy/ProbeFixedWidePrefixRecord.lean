import OAI.Hierarchy.ProbeFixedWidePrefixReceipt

namespace OAI
/-! # Prefix replay from the settlement reconciliation and its native execution -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ) (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
  (compile : Event → List PaidWidths.Slice)

local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "start" => v.catalystStaticStart P h width
local notation "rows" => (P).catalogue.rows
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "original" => TerminalLayout.reserve start cnt page
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (StripDirectory.PayloadRole (Stages h D) k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r banks src (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages banks (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "supply" => fuel v.mesh*width
local notation "C" => v.wideSignedChart h width stock
local notation "o" => wideRouteOrder h D k
local notation "market" => v.catalystMarkets P h width
local notation "words" => v.wideSignedWords h width stock M π o raw
local notation "mid" => Boot.booted market size words
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o raw
local notation "ss" => (events v.mesh).flatMap compile
local notation "paidArchive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (banks).width rows src ss chk))

attribute [local irreducible] CatalystArchive.issued CatalystArchive.recordCount
  CatalystArchive.nativeSite CatalystArchive.debit Procedure.Exec

set_option maxRecDepth 8192 in
set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
/-- Append the public prefix reporters to the settlement whose stored debit, owner and
execution are given by the two native receipts. -/
theorem wide_prefix_from_record (extent : (A).endAddress v.mesh ≤ size) (wordRoom : 28*2^page<2^w)
    {dates : Dates («w» := w) C mid L pay num width} {pos : 0<num}
    (live : Calendar.mounted C (events v.mesh) mid) (paid : PaidWidths.Mounted (banks).width rows src ss chk)
    {I J : Type*} [Fintype I] [Fintype J] {core : I → List (Fin rows)} {center : J → List (Fin rows)}
    {enum : Fin r ≃ RouteOccurrence core center} {ci : I → ℕ} {cj : J → Fin num}
    (maxRows : ℕ) (room : (v.wideReserveLayout h width ss).scratch+2*max maxRows cnt<2^w)
    (lengths : ∀ e ∈ ss, PaidWidths.Slice.count e ≤ maxRows)
    (sized : ∀ e : Fin rows, PaidWidths.total ss chk e<2^w)
    (record : Whole.Reconciliation sink original supply (nativeSite L v.mesh (CatalystArchive.issued dates) pos chk)
      (debit v.mesh (CatalystArchive.issued dates)) enum ci cj paidArchive)
    (execution : (v.wideSettledBody h width ss).Exec (Boot.initial market size words)
      ((sink).output (ReserveUse.output original banks supply (nativeSite L v.mesh (CatalystArchive.issued dates) pos chk)
        (debit v.mesh (CatalystArchive.issued dates)) paidArchive) enum ci (fun j => (cj j).val))
      (v.wideSettledTime h width ss)) :
    let issues := CatalystArchive.issued dates
    let owner := nativeSite L v.mesh issues pos chk
    let duration := debit v.mesh issues
    let settled := (sink).output (ReserveUse.output original banks supply owner duration paidArchive) enum ci
      (fun j => (cj j).val)
    let lw := v.wideWidthLayout h width ss
    let lr := v.wideReserveLayout h width ss
    let a := v.wideReplayArchive h width ss
    let last := (events v.mesh).length
    let sub := PrefixWidths.prefixRows (events v.mesh) compile
    let final := PrefixReserve.image lr banks a (PrefixReserve.countAt v.mesh issues) supply owner duration
      (PrefixWidths.image lw sub settled last) last
    (v.widePrefixBody h width compile).Exec (Boot.initial market size words) final (v.widePrefixTime h width compile) ∧
      (∀ x < lw.archive, final x = settled x) ∧
      (∀ j ≤ last, ∀ e : Fin rows, (final ((lw.bank j).base+e.val)).val = PaidWidths.total (sub j) chk e) ∧
      (∀ j ≤ last, ∀ i : Fin num, (final ((PrefixReserve.banks lr banks j).used.base+i.val)).val =
        (∑ l : Fin (recordCount v.mesh issues), if ((rank v.mesh issues).symm l).1.val<j ∧
          site v.mesh issues l=i then duration l else 0) ∧
        (final ((PrefixReserve.banks lr banks j).reserved.base+i.val)).val = supply) :=
  @wide_append_for_dates F _ k p q Q σ Λ v h width size M π raw compile (v.wideSettledBody h width ss)
    (v.wideSettledTime h width ss) extent wordRoom dates pos live paid I J _ _ core center enum ci cj
    maxRows room lengths sized record execution

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
