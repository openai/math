import OAI.Hierarchy.DescentNamedProfileMatcherBill
import OAI.Hierarchy.DescentProfiledOrdinaryOffer
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # Loading the selected epoch profile into its attained ordinary matcher -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentResetInvoice Chronology
open Chronology.RegisterTimeline DescentPacking.PackedMatch.Local.Stage DescentDatedAddressBook DescentPackedProfileInstall
open DescentMixedRouter Filter
open ThreeFlat.Routing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
  (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg=>ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg=>Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg=>stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))
local notation "k_" h:arg=>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "shelf_" x:arg=>(x).slot.menu.profile (x).slot.age
local notation "seats_" x:arg=>(x).slot.menu.seats (x).slot.age

def archiveProfileLead (ratio : ℕ) := 262144*ratio*(DescentPackedEpochShelves.unit G.C+1)
def archiveProfileRate := (t+1)*(hostRate t reset+capRate G t g+1)+11+(donorRates G t f g reset).amount

/-- The old profile is read at the attained shelf and written at the raw input
of this matcher's installed phase. Both addresses are operands of the native loader. -/
theorem archive_profile_rows {h : ℕ} (x : idx h) (ratio w : ℕ)
    (room : MatcherRoom G (S_ h x) (k_ h) x.slot.p h) (word : w≤ratio*h)
    (large : 64≤h) (oldFit : 2*DescentPackedEpochShelves.unit G.C≤h/2) :
    let H:=(S_ h x).hostSize x.slot.age
    let K:=(S_ h x).groupCount x.slot.age*(S_ h x).radix
    let c:=archiveProfileLead G ratio*scale (J_ h) (archiveProfileRate G t f g reset)
    (x.model.archivePhase x.slot.position.floor (shelf_ x) w).wordInvoice ≤ H*h*c+H*K*c :=by
  intro H K c
  let z:=x.cut
  let S:=S_ h x
  let J:=J_ h
  let date:=DonorDate.atDate G S g (k_ h) x.slot.age x.slot.p
  let area:=date.schedule h (seats_ x) (S.censusBits x.slot.p)
  let root:=x.slot.position.floor
  let old:=x.slot.position.ports.io.roster
  let A:=DescentPackedEpochShelves.grain (h/2) G.C
  let B₀:=area.lanesAt*area.shapeAt.pairs
  let bits:=DescentTerminalEpochBits.width G.C
  let src:=sourceBank (shelf_ x) (seats_ x) A
  let price:=scale J (archiveProfileRate G t f g reset)
  let unit:=DescentPackedEpochShelves.unit G.C
  have dated : x.model.area=area:=congrArg PhysicalOrdinary.StaticCore.area x.core
  have capacity : seats_ x ≤ S.length*S.batch:=x.seats.trans
    (Nat.le_mul_of_pos_left _ (show 0<S.length from Nat.zero_lt_of_lt x.slot.active))
  have native:=Branch.mounted_profile_bill z.original G S z.branch z.ticket z.before z.after z.joined
    h (seats_ x) ratio w x.stageFloor root old src (t:=t) (J:=J) (resetRate:=reset)
    (M:=x.slot.sites) (tailBits:=tail τ J) rfl rfl room word large oldFit x.slot.active.le capacity
  have actual : (x.model.archivePhase root (shelf_ x) w).wordInvoice ≤
      H*h*(262144*ratio)+H*K*(price*(131072*ratio*(unit+1))) :=by
    change (DescentPackedProfileRepack.ticks root (seats_ x) A B₀ bits src
      ((x.model.area.matcher old x.stageFloor).raw)+
      7*DescentStaticWordColumn.names (DescentPackedProfileRepack.program root (seats_ x) A B₀ bits
        x.model.area.shapeAt.digit src ((x.model.area.matcher old x.stageFloor).raw) w))*w≤_
    rw [dated]
    exact native
  have paid : 262144*ratio≤archiveProfileLead G ratio:=
    Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)
  have both : 131072*ratio*(unit+1)≤archiveProfileLead G ratio:=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 131072≤262144))
  have pricePos : 0<price:=Nat.two_pow_pos _
  exact actual.trans (Nat.add_le_add (Nat.mul_le_mul_left _ (paid.trans (Nat.le_mul_of_pos_right _ pricePos)))
    (Nat.mul_le_mul_left _ (by rw [Nat.mul_comm price];exact Nat.mul_le_mul_right _ both)))

/-- One headroom cutoff handles every old profile in the original calendar.
The coefficient and exponent are chosen before the frozen tail and height. -/
theorem eventual_archive_profile_rows (den : 0<B)
    (headroom : 2*((2+hostRate t reset*(t+1)+
      ((donorRates G t f g reset).amount+(donorRates G t f g reset).work)+1+1)+5+0)≤B) :
    ∀ᶠ h : ℕ in atTop, ∀ (x : idx h) (ratio w : ℕ), 2^h≤x.slot.sites → w≤ratio*h →
      let H:=(S_ h x).hostSize x.slot.age
      let K:=(S_ h x).groupCount x.slot.age*(S_ h x).radix
      let c:=archiveProfileLead G ratio*scale (J_ h) (archiveProfileRate G t f g reset)
      (x.model.archivePhase x.slot.position.floor (shelf_ x) w).wordInvoice ≤ H*h*c+H*K*c :=by
  filter_upwards [matcher_room_at G t f g reset 0 τ B den headroom,
    eventually_ge_atTop (max 64 (4*DescentPackedEpochShelves.unit G.C))] with h rooms high
  intro x ratio w ambient bus
  have matcher:=rooms x.slot.sites x.slot.p (show 2^h≤2*x.slot.sites by omega) x.slot.grainLimit
  exact archive_profile_rows G board op t f g reset τ drift degreeMax B x ratio w matcher bus
    ((Nat.le_max_left ..).trans high) (by have:=(Nat.le_max_right ..).trans high;omega)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
