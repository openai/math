import OAI.Hierarchy.ProbeFixedWidePaidRows
import OAI.Hierarchy.ProbeFixedWideStockRun
import OAI.Hierarchy.ProbeFixedWidePayloadRows
import OAI.Hierarchy.ProbeFixedWideRowBoards
import OAI.Hierarchy.ProbeFixedModeLifetimes

namespace OAI
/-! # Uniform native paid widths at every admitted physical date and row -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute StripChart
open PurchaseFrozen StripDirectory CatalystArchive BoughtSockets ReportSockets CatalogueRows PurchaseStage StockCommit
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
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
local notation "chart" => v.wideSignedChart h width stock
variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "mid" => v.wideSignedMidAt h width size stock v.radius π order raw
local notation "out" => v.wideSignedCheckoutAt h width size stock v.radius π order raw
local notation "days" => v.birthMarks P h width r banks src tab dst owners mid
local notation "fmt" => v.nativeFormats P h width
local notation "gs" => v.stamp P h width r banks src tab dst owners
local notation "tr" => v.nativeTrees P h width
local notation "ord" => (P).catalogue.ordinal v.sampler π v.depth days (v.wideOrder h width) rfl

structure PaidPairCells (tape : Memory w) (a : Attempt) (e : Fin (P).catalogue.rows) : Prop where
  direct : (PaidWidths.paidDirect (fmt a).pricedArea (fmt a).stockSource (gs a)).load tape e≤v.paidRoleRate*width
  mate : ∀mask edge,(tr a).catalystMate=some (mask,edge) →
    (PaidWidths.paidMate (fmt a).pricedArea (fmt a).stockSource mask edge).load tape e≤v.paidRoleRate*width
  direct_original : (PaidWidths.paidDirect (fmt a).pricedArea (fmt a).stockSource (gs a)).Positive tape e →
    ∃c,ord c=e
  mate_original : ∀mask edge,(tr a).catalystMate=some (mask,edge) →
    (PaidWidths.paidMate (fmt a).pricedArea (fmt a).stockSource mask edge).Positive tape e → ∃c,ord c=e

def WidePrintedPairCap : Prop :=
  ∀a, Event.attempt a∈events v.mesh → ∀e : Fin (P).catalogue.rows,
    v.PaidPairCells h width size π raw (run chart (events v.mesh) mid) a e ∧
      v.PaidPairCells h width size π raw out a e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3500000 in
theorem wide_printed_pair_cap_at (extent : (A).endAddress v.mesh≤ size) (small : width≤2^h)
    (budget : v.keepLimit*width+1≤2^h) (big : v.wideStockHeight≤h)
    (cutRoom : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤h) (rowRoom : (P).catalogue.rows<2^w)
    (faceRoom : Fintype.card (Columns h D)≤2^w ∧ Stages h D≤2^w ∧ v.sampler.degree≤2^w) :
    v.WidePrintedPairCap h width size π raw := by
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  intro a dated e
  let W:=wordBits h (2^v.W) Native.copies
  have sizes:=v.wide_stock_sizes h width big budget small
  have limits:=sizes.words.addresses
  have inventory:=v.wide_stock_at h width size extent v.radius π raw big budget small
  have whole:=inventory.mounted_all
  let m:=mid
  obtain ⟨_,_,boot,pub,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock v.radius π order raw limits
  have layout (a : Attempt) (ok : Event.attempt a∈events v.mesh) :=
    (v.wide_stock_layout h width size extent v.radius π raw sizes.words budget sizes.width
      sizes.alphabet sizes.rowsMass sizes.roles a ok).1
  have archive:=v.mode_archive P h width r banks src tab dst owners m inventory layout
  have first:=v.wide_paid_run_reads h width r banks src tab dst owners π m boot pub limits whole
  have last:=v.wide_paid_checkout_reads h width r banks src tab dst owners π m ((A).endAddress v.mesh)
    boot pub limits whole le_rfl
  obtain ⟨prior,tail,split⟩:=List.append_of_mem dated
  let entry:=run chart prior m
  have slot:=slot_of_split chart m (.attempt a) prior tail entry split rfl whole
  have existsPair : ∃mask mate,(tr a).catalystMate=some (mask,mate) := by cases a <;> exact ⟨_,_,rfl⟩
  obtain ⟨mask,mate,issued⟩:=existsPair
  have onTape (tape : Memory W) (reads : v.WidePaidReadout h width r banks src tab dst owners π m tape) :
      v.PaidPairCells h width size π raw tape a e := by
    have all:=v.wide_paid_at h width r banks src tab dst owners π m tape reads boot pub limits whole archive
      sizes.strip small cutRoom rowRoom faceRoom.1 faceRoom.2.1 faceRoom.2.2 sizes.roles a prior tail
      entry slot (layout a dated) e
    have one:=all mask mate issued
    exact ⟨one.1.1,fun x y ok=>(all x y ok).1.2,one.2.1,fun x y ok=>(all x y ok).2.2⟩
  exact ⟨onTape _ first,onTape _ last⟩

theorem wide_printed_pair_cap : ∀ᶠ h : ℕ in Filter.atTop,∀width : ℕ,width≤2^h → v.keepLimit*width+1≤2^h →
    ∀size : ℕ,(v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤ size →
    ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),v.WidePrintedPairCap h width size π raw := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [v.wide_row_room,v.wide_face_room,Filter.eventually_ge_atTop v.wideStockHeight,
    Filter.eventually_ge_atTop ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊] with h rowRoom faceRoom big cutRoom
  intro width small budget size extent π raw
  exact v.wide_printed_pair_cap_at h width size π raw extent small budget big cutRoom (rowRoom width).1 faceRoom

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
