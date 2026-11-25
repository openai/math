import OAI.Hierarchy.ProbeFixedReadbackRun
import OAI.Hierarchy.ProbeFixedWideStockOrigin
import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProbeFixedWideBirthRows

namespace OAI
/-! # Real signed chart readbacks on the finite tape used at checkout -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "r" => Fintype.card (Slots h D k)
local notation "decl" => declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "owners" => sinkBank (v.catalystStaticStart P h width) cnt r (P).catalogue.rows
local notation "bits" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "src" => TerminalLayout.source bits
local notation "tab" => TerminalLayout.table bits
local notation "dst" => TerminalLayout.destination bits
local notation "order" => wideRouteOrder h D k
local notation "slots" => max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k))

local notation "f" => v.nativeFormats P h width
local notation "g" => v.stamp P h width r banks src tab dst owners

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Assemble the accepted-run readback from its actual chronological inventory
execution and the two kinds of native strip rows on that same tape. -/
def wide_readback_of_rows
    (size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D)
    (room : (A).endAddress v.mesh < 2^w) (small : width ≤ 2^h) (floor : v.widthFloor ≤ width)
    (stride : v.keepLimit*width+1 ≤ 2^h) (dimension : 2*v.keepLimit+2 ≤ 2^h)
    (ports : slots ≤ 2^w) (letters : v.menu.alphabet ≤ 2^w)
    (copies : v.menu.copiesAt v.copyScale width < 2^w)
    (mass : v.menu.alphabet*v.menu.copiesAt v.copyScale width < 2^w)
    (inventory : StockBound.Run C (v.stockBanks P h width) (v.wideSignedMidAt h width size stock v.radius π order raw) h N k (v.keepLimit*width))
    (valid : admissible C (events v.mesh) (v.wideSignedMidAt h width size stock v.radius π order raw))
    (layout : ∀ a, Event.attempt a ∈ events v.mesh →
      StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)))
    (outer : ∀ p : Fin (v.mesh.inject+v.mesh.cool), ∀ u : Fin v.mesh.outerFuel,
      v.PayloadRepairGeometry P h width r banks src tab dst owners p u (trialState C (v.wideSignedMidAt h width size stock v.radius π order raw) p u))
    (inner : ∀ p : Fin (v.mesh.inject+v.mesh.cool), ∀ u : Fin v.mesh.outerFuel,
      ∀ j : Fin v.mesh.reserveSteps, ∀ t : Fin v.mesh.innerFuel,
      v.PurchasedRepairGeometry P h width r banks src tab dst owners p u j t (innerState C (v.wideSignedMidAt h width size stock v.radius π order raw) p u j t)) :
    v.ReadbackRun P h width r banks src tab dst owners π (v.wideSignedMidAt h width size stock v.radius π order raw) (v.wideSignedMidAt h width size stock v.radius π order raw) := by
  let m := v.wideSignedMidAt h width size stock v.radius π order raw
  letI : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  obtain ⟨_,receipt,seen,econ,fee,prices,_,_,_⟩ :=
    v.wide_signed_boot_at h width size extent stock v.radius π order raw room
  have pages := v.wide_stock_pages h width size extent stock v.radius π order raw r banks src tab dst owners
    ports letters copies mass econ
  have prefixBounds := v.wideGeometryPrefix h width
  have initial := v.catalyst_initial_le_first P h width
  have keyEnd := (BoughtSockets.Public.borders v.sampler (P).routes.column h v.W k v.wideJobs v.depth).2
  have headLow : (BoughtSockets.Public.keyHead v.sampler (P).routes.column h v.W k v.depth).stop ≤ (A).first :=
    keyEnd.trans ((Nat.le_add_right ..).trans (prefixBounds.2.2.trans initial))
  exact {
    nativeStock := inventory
    valid := valid
    resident := econ
    prices := prices
    charges := fee
    steps := rfl
    precision := rfl
    digitBudget := rfl
    payload := small
    widths := floor
    stride := stride
    dimension := dimension
    endFits := room
    heap := prefixBounds.2.1.trans initial
    geometry := receipt.geometry
    keys := fun _ _ => ⟨headLow,seen.board.rom.keys⟩
    slices := ⟨m,pages.1⟩
    boards := fun a scheduled => ⟨layout a scheduled,pages.2 a⟩
    payloadRows := outer
    boughtRows := inner
    purchased := v.wide_birth_rows h width r banks src tab dst owners π m seen inventory.mounted_all room
  }


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
