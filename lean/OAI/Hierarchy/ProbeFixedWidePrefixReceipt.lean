import OAI.Hierarchy.ProbeFixedWidePrefixDirectory
import OAI.Hierarchy.ProbeFixedWidePrefixRoom
import OAI.Hierarchy.ProbeFixedWidePrefixProgram

namespace OAI
/-! # The authenticated fixed settlement continued through all original prefix reporters -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
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
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h



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

variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "mid" => Boot.booted market size (v.wideSignedWords h width stock M π o raw)
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o raw


variable (compile : Event→List PaidWidths.Slice)
local notation "ss" => (events v.mesh).flatMap compile
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "a" => v.wideReplayArchive h width ss
local notation "words" => v.wideSignedWords h width stock M π o raw
local notation "input" => Boot.initial market size words

set_option maxRecDepth 8192 in
set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
/-- This specialization consumes the actual settlement witness and all its dated strips.
The caller can use every old terminal cell and every newly computed count on the same state. -/
theorem wide_append_for_dates (beginning : Procedure w) (beginTicks : ℕ) (extent : (A).endAddress v.mesh ≤ size) (wordRoom : 28*2^page<2^w)
    {dates : Dates («w»:=w) C mid L pay num width} {pos : 0<num}
    (live : Calendar.mounted C (events v.mesh) mid) (paid : PaidWidths.Mounted (old).width rows (TerminalLayout.source page) ss chk)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    {enum : Fin r≃RouteOccurrence core center} {ci : I→ℕ} {cj : J→Fin num}
    (maxRows : ℕ) (room : (lr).scratch+2*max maxRows cnt<2^w)
    (lengths : ∀e∈ss,PaidWidths.Slice.count e≤ maxRows)
    (sized : ∀e : Fin rows,PaidWidths.total ss chk e<2^w) :
    let issues:=CatalystArchive.issued dates
    let nativeOwner:=nativeSite L v.mesh issues pos chk
    let dur:=debit v.mesh issues
    let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    let settled:=(sink).output (ReserveUse.output original old supply nativeOwner dur archive) enum ci (fun j=>(cj j).val)
    Whole.Reconciliation sink original supply nativeOwner dur enum ci cj archive →
    beginning.Exec input settled beginTicks →
    let sub:=PrefixWidths.prefixRows (events v.mesh) compile
    let sizeAt:=PrefixReserve.countAt v.mesh issues
    let final:=PrefixReserve.image lr old a sizeAt supply nativeOwner dur (PrefixWidths.image lw sub settled last) last
    ((beginning.seq (PrefixWidths.program lw sub w last)).seq
      (PrefixReserve.program lr old a (PrefixReserve.publicCount v.mesh decl) supply w last)).Exec input final
        ((beginTicks+PrefixWidths.time lw sub last)+PrefixReserve.cost num (PrefixReserve.publicCount v.mesh decl) last) ∧
      (∀ x<(lw).archive,final x=settled x) ∧
      (∀ j≤last,∀e : Fin rows,(final (((lw).bank j).base+e.val)).val=PaidWidths.total (sub j) chk e) ∧
      (∀j≤last,∀i : Fin num,(final ((PrefixReserve.banks lr old j).used.base+i.val)).val=
        (∑ l : Fin (recordCount v.mesh issues),if ((rank v.mesh issues).symm l).1.val<j ∧
          site v.mesh issues l=i then dur l else 0) ∧
        (final ((PrefixReserve.banks lr old j).reserved.base+i.val)).val=supply) := by
  intro issues nativeOwner dur archive settled certificates exec sub sizeAt final
  let B:=2^page
  have bound : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<B:=Nat.lt_log2_self
  unfold TerminalLayout.footprint at bound
  have dateWord : (A).endAddress v.mesh<2^w := by change 28*B<2^w at wordRoom;omega
  have countWord : num<2^w := by change 28*B<2^w at wordRoom;omega
  have active (i) (positive : 0<debit v.mesh issues i) : nativeOwner i=site v.mesh issues i :=
    nativeSite_from_portROM C A mid ((A).endAddress v.mesh) L issues pos countWord live
      (fun e x hx=>(v.event_prefix P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
        (TerminalLayout.destination page) (sinkBank start cnt r rows) e x hx).1)
      (v.catalyst_owner_args h width _ _ _ _ (P).joint (P).catalogue (v.wideSources h width).2 own
        (v.wideGeometryPrefix h width).2.2 dateWord)
      (fun i=>(Nat.le_add_right ..).trans ((A).within v.mesh _ ((events v.mesh).get_mem i)))
      (issued_port dates) i positive
  have replayDirectory:=v.wide_final_directory_at h width size M π raw extent wordRoom ss (lr).scratch dates pos
    live paid enum ci cj certificates
  have below (x : ℕ) (hx : x<(old).width.base) : settled x=chk x := by
    have low : x<B := by simpa [TerminalLayout.settlement,TerminalLayout.page,B] using hx
    exact TerminalLayout.settled_below_at v.mesh A (P).catalogue L stock stride start cnt supply nativeOwner dur
      v.sampler v.wideJobs (routeBanks start cnt r) g enum ci (fun j=>(cj j).val) chk ss x rfl low paid
  have mountedFile:=PaidWidths.mounted_frame (old).width rows (TerminalLayout.source page) ss chk settled paid below
  obtain ⟨arch,later,apart,wide,split,temporary,available⟩:=v.wide_prefix_slots h width ss maxRows room
  have ready:=PrefixWidths.ready_of_original lw (events v.mesh) compile settled (old).width (TerminalLayout.source page)
    maxRows mountedFile arch later apart wide lengths (fun e=>(PaidWidths.total_frame (old).width
      (TerminalLayout.source page) ss chk settled e (fun t ht=>(paid t ht).1) below).le.trans_lt (sized e))
  have nEq : recordCount v.mesh issues=cnt := recordCount_rowOnly v.mesh issues decl (issued_rows dates)
  have clear : (a).scratch+2*recordCount v.mesh issues<2^w := by rw [nEq];exact available
  have pre := PrefixReserve.after_widths_native v.mesh issues compile lw lr old a
    beginning input settled beginTicks exec ready nativeOwner active
    replayDirectory (v.wide_prefix_fixtures h width ss (by omega)) split temporary clear certificates.word
  obtain ⟨ran,kept,read,usedAt⟩:=pre
  rw [PrefixReserve.public_program_eq v.mesh issues decl (issued_rows dates),
    public_cost v.mesh issues decl (issued_rows dates)] at ran
  refine ⟨ran,kept,?_,usedAt⟩
  intro j hj e
  refine (read j hj e).trans (PaidWidths.total_frame (old).width (TerminalLayout.source page) (sub j) chk settled e ?_ below)
  intro t ht
  apply (paid t ?_).1
  obtain ⟨ev,earlier,hs⟩:=List.mem_flatMap.mp ht
  exact List.mem_flatMap.mpr ⟨ev,List.take_subset j (events v.mesh) earlier,hs⟩

abbrev wide_prefix_for_dates := v.wide_append_for_dates h width size M π raw compile
  (v.wideSettledBody h width ss) (v.wideSettledTime h width ss)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
