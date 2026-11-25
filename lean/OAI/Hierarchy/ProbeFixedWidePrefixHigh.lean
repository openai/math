import OAI.Hierarchy.ProbeFixedWidePrefixUpper
import OAI.Hierarchy.ProtocolRAMCalendarPrefixUpper

namespace OAI
/-! # Original high ROM after both authentic chronological prefix reporters -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
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


local notation "compile" => v.wideEventSlices h width bits
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "a" => v.wideReplayArchive h width ss

theorem wide_prefix_high_for_dates (extendsTape : full ≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    {dates : Dates C mid L pay num width} {pos : 0<num}
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    {enum : Fin r≃RouteOccurrence core center} {ci : I→ℕ} {cj : J→Fin num}
    (maxRows : ℕ) (room : (lr).scratch+2*max maxRows cnt<2^w)
    (lengths : ∀t∈ss,t.count≤ maxRows) (sized : ∀e : Fin rows,PaidWidths.total ss chk e<2^w) :
    let issues:=CatalystArchive.issued dates
    let nativeOwner:=CatalystArchive.nativeSite L v.mesh issues pos chk
    let dur:=CatalystArchive.debit v.mesh issues
    let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    let settled:=(sink).output (ReserveUse.output original old supply nativeOwner dur archive) enum ci (fun j=>(cj j).val)
    Whole.Reconciliation sink original supply nativeOwner dur enum ci cj archive →
    let sub:=PrefixWidths.prefixRows (events v.mesh) compile
    let final:=PrefixReserve.image lr old a (PrefixReserve.countAt v.mesh issues) supply nativeOwner dur
      (PrefixWidths.image lw sub settled last) last
    ∀x, (lr).scratch+2*max maxRows cnt≤x → x<size → final x=raw x := by
  intro issues nativeOwner dur archive settled receipt sub final x above inside
  have paid:=v.wide_funded_paid_at_size h width M π raw bits size extendsTape height budget small
  have below (x : ℕ) (hx : x<(old).width.base) : settled x=chk x := by
    have low : x<2^page := by simpa [TerminalLayout.settlement,TerminalLayout.page] using hx
    exact TerminalLayout.settled_below_at v.mesh A (P).catalogue L stock stride start cnt supply nativeOwner dur
      v.sampler v.wideJobs (routeBanks start cnt r) g enum ci (fun j=>(cj j).val) chk ss x rfl low paid
  have mountedFile:=PaidWidths.mounted_frame (old).width rows (TerminalLayout.source page) ss chk settled paid below
  obtain ⟨arch,later,apart,wide,split,temporary,available⟩:=v.wide_prefix_slots h width ss maxRows room
  have ready:=PrefixWidths.ready_of_original lw (events v.mesh) compile settled (old).width (TerminalLayout.source page)
    maxRows mountedFile arch later apart wide lengths (fun e=>(PaidWidths.total_frame (old).width
      (TerminalLayout.source page) ss chk settled e (fun t ht=>(paid t ht).1) below).le.trans_lt (sized e))
  have nEq : recordCount v.mesh issues=cnt := recordCount_rowOnly v.mesh issues decl (issued_rows dates)
  have prefixCount (j : ℕ) (hj : j≤last) (t : PaidWidths.Slice) (ht : t∈sub j) : t.count≤ maxRows := by
    obtain ⟨e,he,mem⟩:=List.mem_flatMap.mp ht
    exact lengths t (List.mem_flatMap.mpr ⟨e,List.take_subset j (events v.mesh) he,mem⟩)
  have low : full≤x := by
    have h₀ : full≤(lw).scratch:=Nat.le_add_right ..
    have h₁ : (lw).scratch≤(lr).scratch:=Nat.le_add_right ..
    omega
  have upper:=PrefixReserve.after_widths_above lw lr sub old a (PrefixReserve.countAt v.mesh issues)
    supply nativeOwner dur settled last maxRows x ready apart prefixCount temporary (Nat.le_add_right ..) le_rfl
    (by rw [nEq];exact above)
  exact upper.trans (v.wide_settled_above h width size M π raw bits extendsTape height budget small
    nEq nativeOwner dur enum ci (fun j=>(cj j).val) x low inside)

section
attribute [local irreducible] CatalystArchive.recordCount CatalystArchive.issued

open Lean Elab Term in
local elab "prefixReportDates " cert:ident : term => do
  let proof ← Meta.getFVarFromUserName cert.getId
  let reconciliation ← Meta.whnf (← Meta.inferType proof)
  unless reconciliation.getAppFn.isConstOf ``Whole.Reconciliation do
    throwError "expected the prefix settlement reconciliation"
  let some recordRows := reconciliation.getAppArgs[7]? | throwError "expected the settlement record count"
  let count ← Meta.whnf recordRows
  unless count.getAppFn.isConstOf ``CatalystArchive.recordCount do
    throwError "expected the native record count"
  let issues ← Meta.whnf count.getAppArgs.back!
  unless issues.getAppFn.isConstOf ``CatalystArchive.issued do
    throwError "expected the dated issues"
  return ← instantiateMVars issues.getAppArgs.back!

set_option maxHeartbeats 3000000 in
/-- Same fixed program and actual observed prefix, together with the immutable memory suffix. -/
abbrev wide_funded_prefix_high_at (extendsTape : full ≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (state : Word w) (maxRows : ℕ)
    (room : (lr).scratch+2*max maxRows cnt<2^w) (lengths : ∀t∈ss,t.count≤ maxRows)
    (sized : ∀e : Fin rows,PaidWidths.total ss chk e<2^w) :=
  let pfx:=v.wide_funded_prefix_at h width M π raw bits size extendsTape height budget small state
    maxRows room lengths sized
  let certificates := pfx.1.1
  let dates := prefixReportDates certificates
  let board := (P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) chk
  let accounts : 0 < Fintype.card (Columns h D)*k :=
    Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0, Nat.two_pow_pos _⟩⟩) v.positive
  let upper:=v.wide_prefix_high_for_dates h width size M π raw bits extendsTape height budget small
    (dates:=dates) (pos:=accounts) (enum:=CoreRoute.enum board o)
    (ci:=PurchaseInventory.slot) (cj:=pairKeys (Columns h D) k) maxRows room lengths sized certificates
  And.intro pfx upper

end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
