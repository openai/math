import OAI.Hierarchy.ProbeFixedGuardPages
import OAI.Hierarchy.ProbeFixedStripSizes
import OAI.Hierarchy.DiscrepancyPaddedCap
import OAI.Hierarchy.TaggedWireCalendarShelf

namespace OAI
/-! # The original menu and its two recommendation bounds at the native ballot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open WireTelescope
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "H" => v.publicHeader P z width
local notation "G" => v.privateArena P z width
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners

theorem slot_menu_ranges (a : Attempt) (prior tail : List Event) (initial entry : Memory W)
    (cut : Slot C initial (.attempt a) prior tail entry) (left right : ℕ)
    (resident : (H).menus.Resident initial)
    (leftRange : (H).menus.left.Capped left initial) (rightRange : (H).menus.right.Capped right initial) :
    let snap := HistogramShelf.snapshot C a entry
    (H).menus.Resident snap ∧ (H).menus.left.Capped left snap ∧ (H).menus.right.Capped right snap := by
  intro snap
  let ord : (H).Ordered := economic_ordered F (v.sized (v.seed P z width) width) v.cost v.mesh P.joint
    P.catalogue P.routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  have top : (H).stop ≤ (G).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have stop : (H).menus.stop ≤ (G).first := ord.payloadTreeBase.le.trans
    ((Nat.le_add_right ..).trans (ord.boughtTreeBase.le.trans ((Nat.le_add_right ..).trans top)))
  have rightStop : (H).menus.right.stop ≤ (H).menus.stop :=
    ord.menuOrdered.second.trans ((Nat.le_add_right ..).trans (ord.menuOrdered.third.trans (Nat.le_add_right ..)))
  have leftStop : (H).menus.left.stop ≤ (H).menus.stop :=
    ord.menuOrdered.first.trans ((Nat.le_add_right ..).trans rightStop)
  have keep (x : ℕ) (bound : x < (H).menus.stop) : snap x = initial x :=
    (v.slot_rows_low P z width r banks src tab dst owners a prior tail initial entry cut x
      (bound.trans_le stop)).2.1
  exact ⟨resident.move ord.menuOrdered (fun x _ hi => keep x hi),
    leftRange.transport (fun x _ hi => keep x (hi.trans_le leftStop)),
    rightRange.transport (fun x _ hi => keep x (hi.trans_le rightStop))⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
