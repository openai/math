import OAI.Hierarchy.ProbeFixedWideRoleExpressions
import OAI.Hierarchy.ProbeFixedWideCountedPrefix
import OAI.Hierarchy.ProbeFixedDatedRoleInput
import OAI.Hierarchy.TaggedWideDatedMask
import OAI.Hierarchy.ProbeFixedWideStockRun
import OAI.Hierarchy.ProbeFixedWideHistorySupported
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueFlags
import OAI.Hierarchy.TaggedWireRolesAfterReplay

namespace OAI
/-! # The literal signed role operands on the final counted-prefix memory -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires WireTelescope StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
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


variable (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "compile" => v.wideEventSlices h width bits
local notation "hi" => v.wideRoleStart h width stock ss
local notation "base" => (sizes).stop hi
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "source" => TerminalLayout.source page
local notation "table" => TerminalLayout.table page
local notation "target" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r rows
local notation "es" => events v.mesh
local notation "cells" => PurchaseInventory.footprint h N k
local notation "K" => Fintype.card (RoleProgram.Old h v.W k rows)

theorem wide_role_id (m : Memory w) (pages : RoleRoom.StockResident (h:=h) (W:=v.W) (k:=k) (edges:=rows) base m)
    (room : K≤2^w) (i : Fin K) :
    (v.wideRoleID h width bits).eval m (i.val:Word w)=
      (DatedRoleInput.number (SettledMatrix.Layout.numbered («r»:=rows) (I:=Goods h v.W k) («A»:=Catalysts h v.W k) i):Word w) := by
  have two : 2<2^w:=by
    have wordBitsBound : 2≤w:=by unfold Native.wordBits;omega
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) wordBitsBound)
  exact DatedRoleInput.id_eval base m ((lw).bank 0) ((lw).bank 0) (PrefixReserve.banks lr old 0).reserved
    (PrefixReserve.banks lr old 0).used pages two room i


theorem wide_role_id_val (m : Memory w) (pages : RoleRoom.StockResident (h:=h) (W:=v.W) (k:=k) (edges:=rows) base m)
    (room : K≤2^w) (i : Fin K) :
    ((v.wideRoleID h width bits).eval m (i.val:Word w)).val=
      DatedRoleInput.number (SettledMatrix.Layout.numbered («r»:=rows) (I:=Goods h v.W k) («A»:=Catalysts h v.W k) i) := by
  have two : 2<2^w:=by
    have wordBitsBound : 2≤w:=by unfold Native.wordBits;omega
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) wordBitsBound)
  exact DatedRoleInput.id_val base m ((lw).bank 0) ((lw).bank 0) (PrefixReserve.banks lr old 0).reserved
    (PrefixReserve.banks lr old 0).used pages two room i ((v.wide_old_rows h width).ge.trans room)

def wideDatedValue (init archive : Memory w) (issued : Attempt→Entry num width) (j : ℕ) :
    RoleProgram.Old h v.W k rows→ℕ :=
  Sum.elim (PaidWidths.total (PrefixWidths.prefixRows es compile j) archive)
    (Sum.elim (DatedRoleInput.currentFlow v P h width r old source table target owners j init)
      (fun a=>fuel v.mesh*width-PrefixReserve.used (CatalystArchive.site v.mesh issued) (CatalystArchive.debit v.mesh issued)
        (PrefixReserve.countAt v.mesh issued j) (pairKeys (Columns h D) k a)))

structure WideDatedPages (init archive final : Memory w) (issued : Attempt→Entry num width) : Prop where
  metadata : RoleRoom.StockResident (h:=h) (W:=v.W) (k:=k) (edges:=rows) base final
  physical : K≤2^w
  low : ∀a<(A).endAddress v.mesh,final a=run C es init a
  flags : ∀j : Fin (P).catalogue.boughtRows, (P).catalogue.bought.flag.eval final (j.val:Word w)=
    (P).catalogue.bought.flag.eval archive (j.val:Word w)
  amount : ∀ j≤(es).length, ∀i : Fin K,
    ((DatedRoleInput.nativeAmount v P h width r old source table target owners base lw lr old j).eval final (i.val:Word w)).val=
      v.wideDatedValue h width bits init archive issued j (SettledMatrix.Layout.numbered i)

variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "init" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "full" => v.wideFundedSize h width bits

set_option maxHeartbeats 3500000 in
theorem wide_dated_pages_for_dates (extendsTape : full ≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    {dates : Dates C init L pay num width} {pos : 0<num}
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    {enum : Fin r≃RouteOccurrence core center} {ci : I→ℕ} {cj : J→Fin num}
    (maxRows : ℕ) (room : (lr).scratch+2*max maxRows cnt<2^w)
    (final : Memory w) :
    let issues:=CatalystArchive.issued dates
    let nativeOwner:=nativeSite L v.mesh issues pos chk
    let dur:=CatalystArchive.debit v.mesh issues
    let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows source ss chk))
    let settled:=(sink).output (ReserveUse.output original old supply nativeOwner dur archive) enum ci (fun j=>(cj j).val)
    Whole.Reconciliation sink original supply nativeOwner dur enum ci cj archive →
    (∀x<(lw).archive,final x=settled x) →
    (∀j≤last,∀e : Fin rows,(final (((lw).bank j).base+e.val)).val=PaidWidths.total (PrefixWidths.prefixRows es compile j) chk e) →
    (∀j≤last,∀i : Fin num,(final ((PrefixReserve.banks lr old j).used.base+i.val)).val=
      (∑t : Fin (recordCount v.mesh issues),if ((rank v.mesh issues).symm t).1.val<j ∧ CatalystArchive.site v.mesh issues t=i then dur t else 0) ∧
      (final ((PrefixReserve.banks lr old j).reserved.base+i.val)).val=supply) →
    v.WideDatedPages h width bits init chk final issues := by
  intro issues nativeOwner dur archive settled receipt keep paid reserved
  have extent:=(v.wide_funded_extent h width bits).trans extendsTape
  have clocks:=v.wide_stock_sizes h width ((le_max_right ..).trans height) budget small
  have stockRun:=v.wide_funded_stock_at_size h width M π raw bits size extendsTape height budget small
  have mounted:=v.wide_funded_paid_at_size h width M π raw bits size extendsTape height budget small
  have card : recordCount v.mesh issues=cnt:=recordCount_rowOnly v.mesh issues decl (issued_rows dates)
  have within:=v.wide_prefix_slots h width ss maxRows room
  have length : K≤(lw).archive:=by
    change (sizes).old ≤ (sizes).ceiling hi
    dsimp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
      RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  have below : (lw).archive≤(lw).scratch:=Nat.le_add_right ..
  have rowsFit : rows≤2^w:=by
    have term:=within.2.2.1 0 (Nat.zero_le _)
    have word:=within.2.2.2.1
    omega
  have labels : K≤2^w:=length.trans (below.trans (by have word:=within.2.2.2.1;omega))
  have axisFit : num≤2^w:=by
    have usable:=within.2.2.2.2.2.1 0 (Nat.zero_le _)
    change ((lr).bank 1).base+num≤(lr).scratch at usable
    omega
  have fuelWord : supply<2^w:=by
    let i:Fin num:=⟨0,pos⟩
    rw [← (reserved 0 (Nat.zero_le _) i).2]
    exact Fin.isLt _
  have metadata:=RoleRoom.retained v.sampler order directory rows hi (v.widePairedWords h width raw) final (by
    intro x lo endAt
    exact (keep x endAt).trans
      (v.wide_settled_seed h width size M π raw bits extendsTape height budget small card nativeOwner dur enum ci
        (fun j=>(cj j).val) x lo (endAt.trans_le extendsTape)))
  have verdictFrame (x : ℕ) (hx : x<(A).endAddress v.mesh) : chk x=run C es init x :=
    ProtocolRAMGeneratedWrite.frame_image ((A).endAddress v.mesh) 1 (historyFlag C es) (run C es init) x (.inl hx)
  have low (x : ℕ) (hx : x<(A).endAddress v.mesh) : final x=run C es init x:=by
    let B:=2^page
    have rawSpace : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<B:=Nat.lt_log2_self
    unfold TerminalLayout.footprint at rawSpace
    have lim : x<2^page:=by dsimp only [B] at rawSpace;omega
    have atBank : x<(old).width.base:=by
      change x<1*2^page
      simpa only [Nat.one_mul] using lim
    have current:=TerminalLayout.settled_below_at v.mesh A (P).catalogue L stock stride start cnt supply nativeOwner dur
      v.sampler v.wideJobs (routeBanks start cnt r) g enum ci (fun j=>(cj j).val) chk ss x rfl lim mounted
    exact (keep x (atBank.trans_le within.1)).trans (current.trans (verdictFrame x hx))
  have boot:=v.wide_signed_boot_at h width size extent stock M π o seed clocks.words.addresses
  have orig:=v.wide_stock_pages h width size extent stock M π o seed r old source table target owners
    clocks.roles clocks.alphabet clocks.copies clocks.mass boot.2.2.2.1
  have two : 2<2^w:=by
    have bits : 2≤w:=by unfold Native.wordBits;omega
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) bits)
  have checkedFrame (x : ℕ) (hx : x<(A).endAddress v.mesh) : final x=chk x :=
    (low x hx).trans (verdictFrame x hx).symm
  have flagFit:=(v.wide_catalogue_sources h width old source table target owners clocks.words.addresses).2.2.2.2.1
  refine ⟨metadata.2.2,labels,low,(fun i=>eval_below _ _ chk final flagFit checkedFrame),?_⟩
  intro j hj i
  exact DatedRoleInput.amount_eval_at v P h width r old source table target owners base lw lr old j
    init init final chk compile issues i metadata.2.2 two labels rowsFit axisFit fuelWord hj
    (v.wide_initial_room h width) clocks.words.addresses stockRun low orig.1 small budget (paid j hj) (reserved j hj)

section
attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit

open Lean Elab Term in
local elab "countedReportDates " cert:ident : term => do
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

set_option maxHeartbeats 4000000 in
/-- The authentic counted compact CPU and its simultaneous dated operand
readbacks use the identical final memory, for every physical source ordinal. -/
abbrev wide_counted_dated_pages (extendsTape : full ≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (state : Word w)
    (maxRows : ℕ) (room : (lr).scratch+2*max maxRows cnt<2^w)
    (lengths : ∀t∈ss,t.count≤ maxRows) (sized : ∀e : Fin rows,PaidWidths.total ss chk e<2^w) :=
  let certified:=v.wide_counted_prefix_at h width size M π raw bits extendsTape height budget small state maxRows room lengths sized
  let certificates:=certified.1.1.1.1
  let dates:=countedReportDates certificates
  let board := (P).catalogue.coreMount π (siteNumber h D k) (v.wideOrder h width) chk
  let accounts : 0 < Fintype.card (Columns h D)*k :=
    Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨.inl ⟨0, Nat.two_pow_pos _⟩⟩) v.positive
  let proofData:=certified.1.1.2
  let pages:=v.wide_dated_pages_for_dates h width bits size M π raw extendsTape height budget small
    (dates:=dates) (pos:=accounts) (core:=board.ordinary) (center:=board.centers)
    (enum:=CoreRoute.enum board o) (ci:=PurchaseInventory.slot) (cj:=pairKeys (Columns h D) k)
    maxRows room _ certificates proofData.2.1 proofData.2.2.1 proofData.2.2.2
  And.intro certified.2.1 pages

end

/-- Concrete purchase support of the original paid archive, at every date,
ensures the acquired-flag mask agrees with the actual decoded amount on
*every* original row, including unused paid rows. -/
theorem wide_role_width_at (initial archive final : Memory w) (issues : Attempt→Entry num width)
    (pages : v.WideDatedPages h width bits initial archive final issues)
    (active : v.WideHistorySupport h width archive bits) (j : ℕ) (hj : j≤last) (i : Fin K) :
    ((v.wideRoleWidth h width bits j).eval final (i.val:Word w)).val=
      v.wideDatedValue h width bits initial archive issues j (SettledMatrix.Layout.numbered i) := by
  let banks:=PrefixReserve.banks lr old j
  let inv:=v.wideRoleInventory h width bits j
  let raw:=DatedRoleInput.nativeAmount v P h width r old source table target owners base lw lr old j
  have measures:=pages.amount j hj i
  have decoded:=DatedRoleInput.decoded base final ((lw).bank j) ((lw).bank j) banks.reserved banks.used
    pages.metadata pages.physical i
  have two : 2<2^w:=by
    apply lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) ?_)
    unfold Native.wordBits
    omega
  have eRoom : rows<2^w:=by
    have card:=v.wide_old_rows h width
    have capacity:=pages.physical
    have nonempty : 0<cells:=by
      unfold PurchaseInventory.footprint
      positivity
    omega
  have seen (purchaseRow : Fin (P).catalogue.boughtRows)
      (positive : 0<PaidWidths.total (PrefixWidths.prefixRows es compile j) archive ((P).catalogue.boughtIndex purchaseRow)) :
      (P).catalogue.bought.flag.eval final (purchaseRow.val:Word w)≠0 := by
    rw [pages.flags]
    intro dormant
    apply Nat.ne_of_gt positive
    apply (P).catalogue.no_dormant_load _ archive purchaseRow _ dormant
    intro t inside
    obtain ⟨e,taken,member⟩:=List.mem_flatMap.mp inside
    exact active e (List.take_subset j es taken) t member
  exact (congrArg Fin.val (DatedRoleInput.mask_supported (P).catalogue inv final raw i decoded eRoom two
    (PaidWidths.total (PrefixWidths.prefixRows es compile j) archive)
    (DatedRoleInput.currentFlow v P h width r old source table target owners j initial)
    (fun a=>fuel v.mesh*width-PrefixReserve.used (CatalystArchive.site v.mesh issues) (CatalystArchive.debit v.mesh issues)
      (PrefixReserve.countAt v.mesh issues j) (pairKeys (Columns h D) k a)) measures seen)).trans measures


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
