import OAI.Hierarchy.TaggedWireFundedExecution
import OAI.Hierarchy.ProbeFixedMenuSnapshot
import OAI.Hierarchy.ProbeFixedElectionRange
import OAI.Hierarchy.ProbeFixedWideMenuRange

namespace OAI
/-! # The native packet and term-count words of each funded election -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged PurchaseStage ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tab" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "C" => v.wideSignedChart h width stock
local notation "order" => wideRouteOrder h D k

variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (π : Equiv.Perm (Row h))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "slots" => (reader).format.slot
local notation "base" => v.wideOrigin h width size seed π
local notation "L" => (reader).format.windows

local notation "batch" a => enabledBatch ((C).layout a) (repair C a)

include extent in
/-- The packet row and its actual term count in the unmodified histogram snapshot. -/
theorem funded_packet_word_of_nonzero {a : Attempt} {future : List Event} {mem : Memory w}
    (hist : CalendarTape.Prefix slots es base (.attempt a :: future) mem) (row : Fin ((C).layout a).candidates)
    (active : (batch a).packet.eval (HistogramShelf.snapshot C a mem) (row.val:Word w) ≠ 0) :
    let snap:=HistogramShelf.snapshot C a mem
    let code:=(batch a).packet.eval snap (row.val:Word w)
    ∃ i : v.widePacketMenuIndex h a, code.val=v.widePacketNumber h a i ∧
      ((batch a).termCount.read snap code).val=v.widePacketTerms h a i ∧
      0< min ((batch a).termCount.read snap code).val v.menu.alphabet := by
  obtain ⟨raw,prior,cut⟩ := (v.wide_funded_cuts h width size extent π seed age budget small hist).1
  let actual := v.wideFundedRaw h width v.maxBits ((L).header es raw seed)
  let initial := v.wideSignedMidAt h width size stock v.radius π.symm order actual
  have sizes := v.wide_stock_sizes h width age budget small
  have original : (E).menus.Resident initial :=
    v.wide_menu_resident_at h width size extent stock v.radius π.symm order actual sizes.words.addresses
  have limits := v.wide_menu_range_at h width size extent stock v.radius π.symm order actual
  obtain ⟨tables,left,right⟩ := v.slot_menu_ranges P h width r banks src tab dst owners a prior future initial mem
    cut _ _ original limits.1 limits.2
  have threshold : v.stripPorts (publicStages v.W)+v.menu.alphabet+(1+v.menuCodes (publicStages v.W))+v.menu.maximum ≤ h :=
    (le_max_left ..).trans sizes.strip
  have count : v.menu.alphabet < 2^w := (show v.menu.alphabet ≤ h by omega).trans_lt
    ((Nat.lt_two_pow_self (n:=h)).trans (v.date_prefix_fit h))
  exact v.elected_packet_word P h width r banks src tab dst owners a _ (row.val:Word w)
    tables left right count active

include extent in
/-- Every funded selection decodes at the snapshot preceding its future histogram choice. -/
theorem funded_packet_word {a : Attempt} {future : List Event} {mem : Memory w}
    (hist : CalendarTape.Prefix slots es base (.attempt a :: future) mem) (row : Fin ((C).layout a).candidates)
    (picked : (batch a).selected (HistogramShelf.snapshot C a mem) (row.val:Word w)) :
    let snap:=HistogramShelf.snapshot C a mem
    let code:=(batch a).packet.eval snap (row.val:Word w)
    ∃ i : v.widePacketMenuIndex h a, code.val=v.widePacketNumber h a i ∧
      ((batch a).termCount.read snap code).val=v.widePacketTerms h a i := by
  obtain ⟨i,code,terms,_⟩ := v.funded_packet_word_of_nonzero h width size extent π seed age budget small hist row picked.2.1
  exact ⟨i,code,terms⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
