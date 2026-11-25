import OAI.Hierarchy.TaggedWideCalendarFirst
import OAI.Hierarchy.TaggedWideOriginalPins
import OAI.Hierarchy.TaggedWideHistoryUnit

namespace OAI
/-! # All first-date equality cells on their authentic external and history pins -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles Tagged TaggedPrune WireTelescope
open WideControlJoin ThreeFlat Routing
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ) (es : List Event)
local notation "d" => 2^v.W
local notation "N" => siteLast h d k+1
local notation "τ" => exposedSite h d k width (CatalystArchive.fuel v.mesh*width)
variable {Ex Se Data : Type} [Fintype Ex] [Fintype Se] [Fintype Data] (G : Gate)
  (cap : Public v.sampler h v.W k v.wideJobs → ℕ)
  (history : Fin ((es.length+1)*Fintype.card ((u : Public v.sampler h v.W k v.wideJobs) × Fin (cap u))) ↪ Data)
  (external : RoutingPin h width (fun _ : Fin k => Fintype.card (Columns h (2^v.W)) * (CatalystArchive.fuel v.mesh * width)) → Ex)

/-- Every original routing pin is checked once, including both endpoints of every reserve pair. -/
theorem wide_entry_price (hw : h≤width) :
    let E:=fun s : Fin N=>EntryOrder.firstNetwork (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
      (w:=width) (R:=CatalystArchive.fuel v.mesh * width) (Se:=Se) v.sampler cap es G history external F s
    (∑ s, ((E s).cells + (E s).internal)) ≤ v.wideExteriorFactor*(2^h*width) := by
  intro E
  have same (s : Fin N) : (E s).cells+(E s).internal=
      (MatchingEntry.fixedNetwork τ F s).cells+(MatchingEntry.fixedNetwork τ F s).internal :=
    EntryOrder.first_cost (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
      (w:=width) (R:=CatalystArchive.fuel v.mesh * width) (Se:=Se) v.sampler cap es G history external F s
  simp_rw [same]
  rw [MatchingEntry.fixedNetwork_cells]
  refine le_trans ?_ (v.original_exterior h width hw)
  let b : Fin k → ℕ := fun _ => Fintype.card (Columns h d) * (CatalystArchive.fuel v.mesh * width)
  calc
    _ = Nat.card (RoutingPin h width b) := Nat.card_eq_fintype_card.symm
    _ ≤ Nat.card (OpenPins h width b) := by
      have sides : Nat.card Bool = 2 := Nat.card_eq_fintype_card.trans Fintype.card_bool
      simp only [RoutingPin, OpenPins, Catalyst.Port, Row, pins, Nat.card_sum, Nat.card_prod,
        Nat.card_fin, sides]
      omega
    _ = _ := Nat.card_eq_fintype_card

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
