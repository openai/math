import OAI.Hierarchy.ProbeFixedWideCountedCode
import OAI.Hierarchy.ProbeFixedWideFromCT
import OAI.Hierarchy.ProtocolRAMCalendarCompactBoot

namespace OAI
/-! # Genuine short-text paid CPU from the original finite signed parent tape -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open ProbeStage.Native (text text_seq)
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
local notation "n" => PrefixReserve.publicCount v.mesh decl
local notation "subs" => PrefixWidths.prefixRows (events v.mesh) compile
local notation "initial" => Boot.initial market size (v.wideSignedWords h width stock M π o seed)


theorem wide_counted_cheap : CheapCode (v.wideCountedPrefix h width bits) :=
  v.wide_from_ct_cheap h width bits _ (Native.Compact.subdivision_cheap h D)

theorem wide_counted_price :
    v.wideCountedTime h width bits≤Native.Compact.constant D*2^h+(last+2)*v.wideAfterCTTime h width bits ∧
    text (v.wideCountedPrefix h width bits)≤Native.Compact.codeBound D+(last+2)*text (v.wideAfterCT h width bits) := by
  have bill:=v.wide_from_ct_price h width bits (Native.Compact.subdivision h D) (Native.Compact.constant D*2^h)
  exact ⟨bill.1,bill.2.trans (Nat.add_le_add_right (Native.Compact.subdivision_text h D) _)⟩

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec

/-- Physical, finite fixed-ROM parent program with a uniform per-height time. Its
true final memory is shared by the signed calendar, output tables and the fresh suffix. -/
abbrev wide_counted_prefix_at (extendsTape : full ≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (state : Word w)
    (maxRows : ℕ) (room : (lr).scratch+2*max maxRows cnt<2^w) (lengths : ∀t∈ss,t.count≤ maxRows)
    (sized : ∀e : Fin rows,PaidWidths.total ss chk e<2^w) :=
  let fullSize:=(v.wide_funded_extent h width bits).trans extendsTape
  let layout:=v.catalyst_market_layout_at P h width size (v.wideGeometryPrefix h width).2.1 fullSize
  let genuine : (Native.Compact.subdivision h D).Exec initial mid (Native.Compact.constant D*2^h) :=
    Boot.compact_start market layout (Nat.two_pow_pos _) π
      (v.wideSignedWords h width stock M π o seed) (v.wide_signed_words_authentic h width stock M π o seed)
  v.wide_from_ct_run h width size M π raw bits extendsTape height budget small state maxRows room lengths sized
    (Native.Compact.subdivision h D) (Native.Compact.constant D*2^h) (@genuine)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
