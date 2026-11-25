import OAI.Hierarchy.TaggedWideNumberedBranchRoles
import OAI.Hierarchy.ProbeFixedWideOriginalRolePages

namespace OAI
/-! # Authenticated branch roles from the original funded settlement -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
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


variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss
local notation "last" => (events v.mesh).length

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
local notation "emb" => DatedRows.embed v.sampler π v.depth days (P).catalogue order cardFit
local notation "catalog" => (P).catalogue.ordinal v.sampler π v.depth days order cardFit
local notation "whereAt" => HistoryRoles.sorted v.sampler π v.depth days
local notation "V" => v.wideDatedValue h width bits mid chk issues


open WireTelescope.CalendarTape
local notation "es" => events v.mesh
local notation "physicalCap" c => HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh c v.keepLimit (fuel v.mesh) width
local notation "excl" => v.paid_days_exclusive h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) mid

/-- Physical scan reads in the exact original funded run. The reconciliation
argument fixes the dependent dates and the public sparse catalogue enumeration. -/
def originalDateFields (_receipt : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (ell unitCost work : ℕ) (image : Memory w) : Prop :=
  letI : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let d:=v.wideDated h width ell unitCost
  ∀t : Fin ((es).length+1),∀f : Fin 3,DatedRoleSheets.roleFact d.physical v.sampler π v.depth days excl names
    (d.roleStart work t) (V t.val ∘ emb ∘ names)
    (fun i=>(sparseKey v.sampler π v.depth days (P).catalogue order cardFit (PurchaseInventory.slotEquiv h N k)
      pair (names i)).val) image f

theorem originalDateFields.after (data : Whole.Reconciliation (n := recordCount (count := num) (payload := width) v.mesh issues) (count := num) («w» := w) sink original supply who dur ord ci pair archive)
    (ell unitCost work : ℕ) {earlier out : Memory w}
    (orig : v.originalDateFields h width size π raw (dates := dates) (pos := pos) data ell unitCost work earlier)
    (preserved : ∀i,i<(v.wideDated h width ell unitCost).rolesEnd work→ out i=earlier i) :
    v.originalDateFields h width size π raw (dates := dates) (pos := pos) data ell unitCost work out := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let d:=v.wideDated h width ell unitCost
  intro t f
  apply d.roleFact_local 0 work v.sampler π v.depth days excl names (fun j:Fin ((es).length+1)=>V j.val ∘ emb ∘ names)
    (fun i=>(sparseKey v.sampler π v.depth days (P).catalogue order cardFit (PurchaseInventory.slotEquiv h N k)
      pair (names i)).val) rfl t f earlier out _ (orig t f)
  intro i _ h
  have ends:=(WideCPU.role_order d 0 work).upper (finProdFinEquiv (t,f))
  simp only [Equiv.symm_apply_apply] at ends
  exact preserved i (h.trans_le ends)


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
