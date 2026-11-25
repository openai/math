import OAI.Hierarchy.DescentNamedMatcherCharge
import OAI.Hierarchy.DescentNamedOrdinaryEntryRoom
import OAI.Hierarchy.DescentProfiledOrdinaryOffer

namespace OAI
/-! # The matcher component of the charged ordinary DateCode at the original physical cut -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentResetInvoice Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch.Local.Stage.Dated
open ThreeFlat.Routing Filter
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F] {G : PoweredGadget F} {n d : ℕ} {board : NonlinearExpanders.Graph n d}
    {op : RotorSpec} {t f g reset τ drift degreeMax B h : ℕ}
local notation "idx" H:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B H
local notation "J_" H:arg => Nat.log 2 H/(2*B)
local notation "tb_" H:arg => tail τ (J_ H)
local notation "S_" H:arg x:arg =>stageNumbers G t (J_ H) f g reset (x:idx H).slot.sites (tb_ H)
local notation "k_" H:arg =>groupBits t (J_ H) (hostRate t reset) (capRate G t g) (cutRate t f g)

def matcherFee (x : idx h) (w : ℕ) : ℕ :=
  let hk : 0<(k_ h):=Nat.add_pos_left (Nat.add_pos_right _ (by decide : 0<8)) _
  let a := x.slot.menu.ordinary x.slot.age
  let vals := measuresAt (S_ h x) G.b x.slot.p x.slot.age
  DateBill.bitTariff (a.program G hk x.slot.position.ports.io vals w x.stageFloor)
    (a.ticks G hk x.slot.position.ports.io vals w x.stageFloor)

theorem matcher_charge (x : idx h) (ratio : ℕ) (word : x.slot.bus≤ratio*h) (embed : h≤x.slot.bus)
    (room : MatcherRoom G (S_ h x) (k_ h) x.slot.p h)
    (guard : max x.endAt (x.model.signedGuard x.stageFloor)<2^x.slot.bus) :
    x.matcherFee x.slot.bus ≤
      ((S_ h x).hostSize x.slot.age*h+(S_ h x).hostSize x.slot.age*((S_ h x).groupCount x.slot.age*(S_ h x).radix))*
        (ratio*scale (J_ h) (matcherChargeRate G t f g reset)) :=by
  have fit:=(Branch.selected_entry_room x.cut.original G (S_ h x) x.cut.branch x.cut.ticket x.cut.before
    x.cut.after x.cut.joined op (tb_ h) drift x.slot.degree h x.slot.position.floor
    x.slot.position.ports x.slot.menu.ordinary board
    x.slot.menu.seats x.slot.menu.profile x.slot.header x.slot.bus embed x.slot.geometry (by exact ⟨rfl,rfl⟩) room
    ((le_max_left ..).trans_lt guard) ((le_max_right ..).trans_lt guard)).1
  have hk : 0<(k_ h):=Nat.add_pos_left (Nat.add_pos_right _ (by decide : 0<8)) _
  exact Branch.matcher_charge x.cut.original G (S_ h x) x.cut.branch x.cut.ticket x.cut.before
    x.cut.after x.cut.joined h (x.slot.menu.seats x.slot.age) ratio x.slot.bus x.stageFloor
    x.slot.position.ports.io hk rfl rfl room
    fit word (fun i=>⟨_,x.slot.geometry.room.paid.issued.row i.val⟩)

variable (G board op t f g reset τ drift degreeMax B)

/-- The time and opcode-text coefficient is chosen before the terminal tail and the CPU width. -/
theorem calibrated_matcher_charge (positive : 0<B)
    (large : 2*((2+hostRate t reset*(t+1)+
      ((donorRates G t f g reset).amount+(donorRates G t f g reset).work)+1+1)+5+0)≤B) :
    ∀ᶠ h : ℕ in atTop, ∀x : idx h, ∀ratio, 2^h≤2*x.slot.sites →
      h≤x.slot.bus → x.slot.bus≤ratio*h →
      max x.endAt (x.model.signedGuard x.stageFloor)<2^x.slot.bus →
      x.matcherFee x.slot.bus ≤
        ((S_ h x).hostSize x.slot.age*h+
          (S_ h x).hostSize x.slot.age*((S_ h x).groupCount x.slot.age*(S_ h x).radix))*
          (ratio*scale (J_ h) (matcherChargeRate G t f g reset)) :=by
  filter_upwards [matcher_room_at G t f g reset 0 τ B positive large] with h calendar
  intro x ratio size embed width ready
  exact x.matcher_charge ratio width embed (calendar x.slot.sites x.slot.p size x.slot.grainLimit) ready

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
