import OAI.Hierarchy.TaggedWideFundedIndexedOperators
import OAI.Hierarchy.TaggedWireActualRoutedSchedule

namespace OAI
/-! # The two stage factorizations for the installed, funded routed schedule -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged CalendarTape ChosenPackets ThreeFlat.RAM
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Filter
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 12000
set_option maxHeartbeats 2100000
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width size : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "K" => siteLast h D k+1
local notation "es" => events v.mesh
local notation "place" => siteNumber h D k
local notation "order" => wideRouteOrder h D k
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
variable (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (π : Equiv.Perm (Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "slots" => (v.wideSelector h width age budget small).format.slot
local notation "L" => (v.wideSelector h width age budget small).format.windows
local notation "state" => v.wideOrigin h width size seed
local notation "base" => (state) π
local notation "origin" key:arg => v.wideOrigin h width size ((L).header es key seed) π
local notation "Visit" ev:arg => WireTelescope.CalendarTape.Prefix.PathVisit slots es base ev
variable (expanse : v.wideFundedSize h width v.maxBits≤ size) (routeAge : v.routingHeight≤h)
    (floor : v.widthFloor≤width) (word : v.ReportWordRoom h width)
local notation "cal" => v.routedSchedule h width size extent seed age budget small expanse routeAge floor word
local notation "beginAt" => (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix slots es base es base)
local notation "cs" => Prefix.cursorSlot (slot:=slots) (events:=es) (x₀:=base)

local notation "atDay" path:arg j:arg => indexedStep cs (Prefix.atWidth ((cal).width π))
  (Prefix.atStep ((cal).width π) ((cal).operator π)) es (Prefix.atCursor beginAt) (Prefix.histories beginAt path) j
local notation "rowAge" => (max_le_iff.mp routeAge).1

/-- The genuine routed schedule supplies both numerically elected row families.
Its indexed gate factors for every external permutation and every original ballot. -/
theorem wide_routed_indexed_operator (path : Path slots es base) (j : Fin (es).length) :
    v.electedOperatorAt h width size extent π seed age budget small (max_le_iff.mp routeAge).1 floor
      ((es).get j) (Prefix.pathVisit beginAt path j)
      (indexedStep cs (Prefix.atWidth ((cal).width π)) (Prefix.atStep ((cal).width π) ((cal).operator π))
        es (Prefix.atCursor beginAt) (Prefix.histories beginAt path) j) := by
  have limits:=max_le_iff.mp routeAge
  have ages:=limits.1
  simp only [rowScheduleHeight,max_le_iff] at ages
  exact v.wide_elected_indexed_operator h width size extent π seed age budget small expanse limits.1 floor word
    (fun p {_ _ _} t=>v.funded_source_rows h width size extent p seed age budget small t
      (max_le_iff.mp limits.1).1 floor expanse ages.2.2.2.2.2.2)
    (fun p {_ _ _} t=>v.funded_target_rows h width size extent p seed age budget small t
      (max_le_iff.mp limits.1).1 floor (max_le_iff.mp limits.2).1 (max_le_iff.mp limits.2).2)
    path j

private theorem recover_attempt {e : Event} {a : Attempt} (ev : e=.attempt a) (z : Visit e)
    {U V : Widths K} (gate : SiteMatrix (State U) (State V) F)
    (present : v.electedOperatorAt h width size extent π seed age budget small rowAge floor e z gate) :
    v.electedAttemptAt h width size extent π seed age budget small rowAge floor
      (cast (congrArg (fun f=>Prefix.PathVisit slots es base f) ev) z) gate := by
  subst e
  exact present

private theorem recover_feed {e : Event} {b : Boundary} (ev : e=.feed b) (z : Visit e)
    {U V : Widths K} (gate : SiteMatrix (State U) (State V) F)
    (present : v.electedOperatorAt h width size extent π seed age budget small rowAge floor e z gate) :
    v.electedFeedAt h width size extent π seed age budget small rowAge
      (cast (congrArg (fun f=>Prefix.PathVisit slots es base f) ev) z) gate := by
  subst e
  exact present

theorem wide_routed_indexed_attempt (path : Path slots es base) (j : Fin (es).length)
    {a : Attempt} (day : (es).get j=.attempt a) :
    v.electedAttemptAt h width size extent π seed age budget small rowAge floor
      (cast (congrArg (fun f=>Prefix.PathVisit slots es base f) day) (Prefix.pathVisit beginAt path j)) (atDay path j) :=
  v.recover_attempt h width size extent π seed age budget small routeAge floor day _ _
    (v.wide_routed_indexed_operator h width size extent π seed age budget small expanse routeAge floor word path j)

theorem wide_routed_indexed_feed (path : Path slots es base) (j : Fin (es).length)
    {b : Boundary} (day : (es).get j=.feed b) :
    v.electedFeedAt h width size extent π seed age budget small rowAge
      (cast (congrArg (fun f=>Prefix.PathVisit slots es base f) day) (Prefix.pathVisit beginAt path j)) (atDay path j) :=
  v.recover_feed h width size extent π seed age budget small routeAge floor day _ _
    (v.wide_routed_indexed_operator h width size extent π seed age budget small expanse routeAge floor word path j)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
