import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMCalendarStripSeen
import OAI.Hierarchy.ProtocolRAMCatalystStripDates

namespace OAI
/-! # Original verdict and signed cash columns remain inside each genuine dated stratum -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart CoreBoard
open BoughtSockets CatalogueRows CatalystArchive StockCommit
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width : ℕ)
local notation "s" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "incoming" => resolvedStock v.mesh A P.joint.initial (build F s)

theorem catalyst_dated_verdict (r : ℕ) (banks : RouteSettlement.Banks) (src table dst : ℕ) (owners : Bank)
    (a : Attempt) :
    let C:=StripChart.chart F v.mesh A P.joint.initial width v.keepLimit (withPorts s v.mesh P.catalogue P.routes)
      v.finish (v.basePhase width) P.catalogue r banks src table dst owners
    (repair C a).verdict<(A).base v.mesh (.attempt a)+(A).stride := by
  intro C
  let f:=v.nativeFormats P z width a
  have eqn : (repair C a).verdict=f.board.verdict := by cases a <;> rfl
  rw [eqn]
  exact (Slab.verdict_before f).trans_le (v.attempt_room P z width a)

theorem catalyst_amount_room (ownerArena : Arena) (e : Event) :
    cashWidthBase F s v.mesh P.catalogue P.routes incoming e+
      (ownerLedger s v.mesh P.catalogue P.routes F ownerArena).rows e≤(A).base v.mesh e+(A).stride := by
  cases e with
  | feed b => exact Nat.zero_le _
  | attempt a =>
    let f:=v.nativeFormats P z width a
    have cash : cashWidthBase F s v.mesh P.catalogue P.routes incoming (.attempt a)=
        f.pricedArea.direct+f.pricedArea.occurrences := by cases a <;> rfl
    have rows : (ownerLedger s v.mesh P.catalogue P.routes F ownerArena).rows (.attempt a)=f.pricedArea.occurrences := by
      cases a <;> rfl
    rw [cash,rows]
    apply le_trans _ (v.attempt_room P z width a)
    change f.pricedArea.direct+f.pricedArea.occurrences+f.pricedArea.occurrences ≤ f.pricedArea.stop
    unfold Area.stop Area.output Area.excess Area.clip Area.src Area.broadcast
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
