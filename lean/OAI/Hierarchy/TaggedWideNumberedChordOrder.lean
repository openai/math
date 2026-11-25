import OAI.Hierarchy.TaggedWideTerminalParallelOrder
import OAI.Hierarchy.TaggedWideNumberedBranchRoles

namespace OAI
/-! # Chronological order on chords of the funded numbered roles -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 550000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
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

local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width

local notation "o" => wideRouteOrder h D k

variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i

local notation "pair" => pairKeys (Columns h D) k
open private reportCost reportDates reportEntries reportSites from
  OAI.Hierarchy.TaggedWideNumberedBranchRoles

variable (horizon : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight ≤ h)
    (budget : v.keepLimit * width + 1 ≤ 2^h) (small : width ≤ 2^h)
    (cost : reportCost v h width size π raw)
local notation "days" => v.birthMarks P h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid
variable {dates : reportDates v h width size π raw} {pos : 0 < Fintype.card (Columns h (2^v.W)) * k}
local notation "issues" => reportEntries v h width size π raw dates

local notation "who" => reportSites v h width size π raw dates pos
local notation "dur" => CatalystArchive.debit (count := num) (payload := width) v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))

local notation "cardFit" => v.wide_dated_bought_rows h width
local notation "names" => timeRows v.sampler π v.depth days (P).catalogue order cardFit pair

open WireTelescope.CalendarTape
local notation "es" => events v.mesh

variable {X : Type} {slot : Event → CalendarTape.Slot X} {initial : X} (unitCost : ℕ)
    (j : CalendarTape.Path slot (events v.mesh) initial)
    (wire : CalendarTape.Prefix.Cursor slot (events v.mesh) initial → Widths (siteLast h (2^v.W) k + 1))

private abbrev RoleDictionary {hh ww dim_ jobs_ : ℕ}
    (sampler_ : PurchaseSampler) (perm_ : Equiv.Perm (Fin (2^hh))) (depth_ : ℕ) :=
  (mark_ : ReportSockets.Marks hh ww dim_ jobs_) × (n_ : ℕ) × (Fin n_ ≃ HistoryRoles.Source sampler_ perm_ depth_ mark_)

private def roleDictionary {Y : Type} {sl : Event → CalendarTape.Slot Y} {events_ : List Event} {base : Y}
    {height wordWidth dim jobs : ℕ} {sampler : PurchaseSampler} {perm : Equiv.Perm (Fin (2^height))}
    {depth : ℕ} {cap : Public sampler height wordWidth dim jobs → ℕ}
    {wired : CalendarTape.Prefix.Cursor sl events_ base → Widths (siteLast height (2^wordWidth) dim + 1)}
    {path : CalendarTape.Path sl events_ base} (R_ : BranchRoles sampler perm depth cap wired path)
    : RoleDictionary (ww := wordWidth) (dim_ := dim) (jobs_ := jobs) sampler perm depth :=
  ⟨R_.mark, R_.count, R_.order⟩

private def dictionaryEarlier {hh ww dim_ jobs_ : ℕ}
    (sampler_ : PurchaseSampler) (perm_ : Equiv.Perm (Fin (2^hh))) (depth_ : ℕ)
    (board_ : CatalogueRows.Board) (code_ : Fin board_.coreRows ≃ Edges sampler_ hh (2^ww) dim_)
    (bound_ : jobs_ * (PurchaseFrozen.count hh (2^ww) dim_ * PurchaseFrozen.paths hh sampler_.degree depth_) = board_.boughtRows)
    (dict_ : RoleDictionary (ww := ww) (dim_ := dim_) (jobs_ := jobs_) sampler_ perm_ depth_) : Prop :=
  ∀ i j : Fin dict_.2.1,
    HistoryRoles.sorted sampler_ perm_ depth_ dict_.1 (dict_.2.2 i) =
    HistoryRoles.sorted sampler_ perm_ depth_ dict_.1 (dict_.2.2 j) →
    (i < j ↔
     DatedRows.raw sampler_ perm_ depth_ dict_.1 board_ code_ bound_ dict_.2.2 i <
     DatedRows.raw sampler_ perm_ depth_ dict_.1 board_ code_ bound_ dict_.2.2 j)

private theorem dictionaryEarlier_of_eq {hh ww dim_ jobs_ axes_ : ℕ}
    (sampler_ : PurchaseSampler) (perm_ : Equiv.Perm (Fin (2^hh))) (depth_ : ℕ)
    (mark_ : ReportSockets.Marks hh ww dim_ jobs_) (board_ : CatalogueRows.Board)
    (code_ : Fin board_.coreRows ≃ Edges sampler_ hh (2^ww) dim_)
    (bound_ : jobs_ * (PurchaseFrozen.count hh (2^ww) dim_ * PurchaseFrozen.paths hh sampler_.degree depth_) = board_.boughtRows)
    (axis_ : Catalysts hh ww dim_ ≃ Fin axes_)
    (dict_ : RoleDictionary (ww := ww) (dim_ := dim_) (jobs_ := jobs_) sampler_ perm_ depth_)
    (shape_ : dict_ = ⟨mark_, Fintype.card (Source sampler_ perm_ depth_ mark_), timeRows sampler_ perm_ depth_ mark_ board_ code_ bound_ axis_⟩) :
    dictionaryEarlier sampler_ perm_ depth_ board_ code_ bound_ dict_ := by
  subst dict_
  exact DatedRows.earlier_on_chord sampler_ perm_ depth_ mark_ board_ code_ bound_ axis_

include horizon age budget small cost

private theorem roleDictionary_at
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (bounded : v.DatedWireFits h width π mid chk unitCost)
    (atTime : ∀i:Fin ((es).length+1),v.wideDatedWire h width bits π mid chk issues i.val=wire (Prefix.boundaryIndex j i)) :
    letI : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
    roleDictionary ((v.numberedBranchRoles h width size π raw horizon age budget small cost unitCost j wire
      (dates:=dates) (pos:=pos) receipt funded bounded atTime)) = ⟨days, Fintype.card (Source v.sampler π v.depth days), names⟩ := by
  rfl

attribute [local irreducible] numberedBranchRoles
/-- On a common chord, the funded role order agrees with the native row address. -/
theorem numberedRoleChordOrder
    (receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (funded : v.WideFundedAlignment h width size bits π raw who dur (fun j=>(pair j).val))
    (bounded : v.DatedWireFits h width π mid chk unitCost)
    (atTime : ∀i:Fin ((es).length+1),v.wideDatedWire h width bits π mid chk issues i.val=wire (Prefix.boundaryIndex j i)) :
    letI : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
    let picked := v.numberedBranchRoles h width size π raw horizon age budget small cost unitCost j wire
      (dates:=dates) (pos:=pos) receipt funded bounded atTime
    dictionaryEarlier v.sampler π v.depth (P).catalogue order cardFit (roleDictionary picked) := by
  let : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  exact dictionaryEarlier_of_eq v.sampler π v.depth days (P).catalogue order cardFit pair _
    (roleDictionary_at v h width size π raw horizon age budget small cost unitCost j wire
      (dates:=dates) (pos:=pos) receipt funded bounded atTime)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
