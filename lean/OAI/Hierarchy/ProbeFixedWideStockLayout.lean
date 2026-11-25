import OAI.Hierarchy.ProbeFixedWideStockOrigin
import OAI.Hierarchy.ProbeFixedWideTestWordRoom
import OAI.Hierarchy.ProbeFixedStockPrefixFits
import OAI.Hierarchy.ProbeFixedPostprocessing
import OAI.Hierarchy.ProbeFixedWideSettlement

namespace OAI
/-! # Static trial layouts and actual starting pages of the signed calendar -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires BoughtSockets
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


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "order" => wideRouteOrder h D k

theorem wide_stratum_before :
    (StripDirectory.stratumHeader h D k v.sampler.degree v.depth (P).routes.directory.keysBase).stop≤(P).joint.initial := by
  let coreStart:=CoreCatalogue.top h v.W (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
  exact (Public.borders v.sampler coreStart h v.W k v.wideJobs v.depth).2.trans
    ((Nat.le_add_right ..).trans (v.wideGeometryPrefix h width).2.2)

/-- Every scheduled trial has the concrete, bounded mask, both snapshot inputs,
and the real original stock-update operands on the authenticated finite input. -/
theorem wide_stock_layout (size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (words : v.TestWordRoom P h width)
    (budget : v.keepLimit*width+1≤2^h) (widthWord : width<2^w) (letters : v.menu.alphabet≤2^w)
    (counter : v.menu.alphabet*width<2^w) (localRoom : slots≤2^w)
    (a : Attempt) (scheduled : Event.attempt a∈events v.mesh) :
    let init:=v.wideSignedMidAt h width size stock M π order raw
    StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)) ∧
      StockBound.Original (f a) (g a) (StripChart.start s a) (A).first init init := by
  intro init
  have «public»:=(v.wide_signed_boot_at h width size extent stock M π order raw words.addresses).2.2.2.1
  have lc : v.menu.copiesAt v.copyScale width≤width:=Nat.div_le_self ..
  have shapes:=v.wide_stock_pages h width size extent stock M π order raw r banks source table target owners
    localRoom letters (lc.trans_lt widthWord) ((Nat.mul_le_mul_left _ lc).trans_lt counter) «public»
  have core:=(v.wideGeometryPrefix h width).2.2
  have board:=(v.fixed_post h width r (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k) 0 (P).joint
    (v.wideSources h width).2 banks source table target owners a scheduled core words.addresses
    words.cut widthWord letters counter).1
  have feasible : v.keepLimit*width<2^w:=(Nat.lt_of_succ_le budget).trans (v.date_prefix_fit h)
  exact ⟨v.stock_trial_layout P h width r banks source table target owners a scheduled words.addresses feasible
    le_rfl (v.stock_prefix_native P h width a (v.wide_stratum_before h width)) board,shapes.2 a⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
