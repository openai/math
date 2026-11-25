import OAI.Hierarchy.DescentProfiledOfferInvoice
import OAI.Hierarchy.DescentNamedOrdinaryEntryRoom
import OAI.Hierarchy.DescentRegisteredSignedSpace
import OAI.Hierarchy.DescentRegisteredReturnInvoice
import OAI.Hierarchy.DescentNamedSignedUnit

namespace OAI
/-! The registered material, roster, mark and signed programs paid by an actual ordinary offer. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale Chronology DescentInitialHost DescentResetInvoice
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open Filter
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] {G : PoweredGadget F} {n d : ℕ} {board : NonlinearExpanders.Graph n d}
  {op : RotorSpec} {t f g reset τ drift degreeMax B h : ℕ}
local notation "offers_" H:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B H
local notation "J_" H:arg => Nat.log 2 H/(2*B)
local notation "frozen_" H:arg => tail τ (J_ H)
local notation "calendar_" H:arg x:arg => stageNumbers G t (J_ H) f g reset (x:offers_ H).slot.sites (frozen_ H)
local notation "bits_" H:arg => groupBits t (J_ H) (hostRate t reset) (capRate G t g) (cutRate t f g)
variable (x : offers_ h)
local notation "z_" => x.slot
local notation "prior_" => (z_).position.ports
local notation "entry_" => x.base.registeredEntry (prior_) x.stageFloor
local notation "sources_" => (⟨(prior_).archive.count,(prior_).io.roster,(prior_).io.hubs⟩:DescentOrdinaryVenueReturn.Sources)

def returnInvoice (room : x.CodeRoom) :=
  (x.model.issuedPrefix x.stageFloor (z_).bus (entry_).venue.panel (entry_).venue.adjacency
    (sources_) (prior_).io room.signed).wordInvoice

def returnCutoff (G : PoweredGadget F) (t f g reset : ℕ) : ℕ :=
  let old := donorRates G t f g reset
  let signed := signedRates G t f g reset
  max (2*((2+hostRate t reset*(t+1)+(old.amount+old.work)+1+1)+5))
    (1+max old.amount (max signed.amount (SignedStage.unitRate G t f g reset)))

variable (G board op t f g reset τ drift degreeMax B)
theorem chosen_return_charge (ratio : ℕ) (positive : 0 < B) (budget : returnCutoff G t f g reset ≤ B) :
    ∀ᶠ h : ℕ in atTop, ∀x : offers_ h, 2^h ≤ 2*x.slot.sites → h ≤ x.slot.bus →
      x.slot.bus ≤ ratio*h → max x.endAt (x.model.signedGuard x.stageFloor) < 2^x.slot.bus →
      ∀room : x.CodeRoom,
      x.returnInvoice room ≤ (calendar_ h x).hostSize x.slot.age*h*((ratio+1)*scale (J_ h) (returnRate G t f g reset))+
        (calendar_ h x).hostSize x.slot.age*((calendar_ h x).groupCount x.slot.age*(calendar_ h x).radix)*
          ((ratio+1)*scale (J_ h) (returnRate G t f g reset)) := by
  dsimp only [returnCutoff] at budget
  have caps := max_le_iff.mp budget
  have old : (donorRates G t f g reset).amount < B := by omega
  have signed : (signedRates G t f g reset).amount < B := by omega
  have fixed : SignedStage.unitRate G t f g reset < B := by omega
  filter_upwards [matcher_room_at G t f g reset 0 τ B positive (by simpa using caps.1),
    AgeBound.payload_room _ B old, AgeBound.payload_room _ B signed,
    SignedStage.unitRate_cofinal G t f g reset B fixed,
    Branch.eventual_return_funding G t f g reset ratio 0] with h matcher past future shape funded
  intro x size embed width guard room
  let S := calendar_ h x
  let k := bits_ h
  let z := x.slot
  let prior := z.position.ports
  let entry := x.base.registeredEntry prior x.stageFloor
  let oldSources : DescentOrdinaryVenueReturn.Sources := ⟨prior.archive.count,prior.io.roster,prior.io.hubs⟩
  have paid := matcher z.sites z.p size z.grainLimit
  have fit := (Branch.selected_entry_room x.cut.original G S x.cut.branch x.cut.ticket x.cut.before
    x.cut.after x.cut.joined op (frozen_ h) drift z.degree h z.position.floor prior z.menu.ordinary board
    z.menu.seats z.menu.profile z.header z.bus embed z.geometry (by exact ⟨rfl,rfl⟩) paid
    ((le_max_left ..).trans_lt guard) ((le_max_right ..).trans_lt guard)).1
  have age : z.age ≤ (t+1)*(J_ h) := z.active.le
  have live : 0 < k := Nat.add_pos_left (Nat.add_pos_right _ (by decide : 0 < 8)) _
  have modelArea : x.model.area = (DonorDate.atDate G S g k z.age z.p).schedule h (z.menu.seats z.age) (S.censusBits z.p) :=
    congrArg PhysicalOrdinary.StaticCore.area x.core
  have actualFit : x.model.area.Space prior.io z.bus x.stageFloor := by
    rw [modelArea]
    exact fit
  have topology := (Branch.registered_signed_room x.cut.original G S x.cut.branch x.cut.ticket x.cut.before
    x.cut.after x.cut.joined op (frozen_ h) drift z.degree h (z.menu.seats z.age) z.position.floor prior z.menu.ordinary
    z.bus live (paid.hosts z.age) (shape z.sites (frozen_ h) z.age (NativePitch.incomingHosts S (z.age+1)) age)
    actualFit ((le_max_right ..).trans_lt guard)).1
  have receipt := Branch.registered_return_funded x.cut.original G S x.cut.branch x.cut.ticket
    x.cut.before x.cut.after x.cut.joined x.books (frozen_ h) h (z.menu.seats z.age) prior.venue.lanes
    prior.io.roster z.menu.ordinary rfl rfl x.stageFloor z.bus ratio entry.venue.panel entry.venue.adjacency
    oldSources prior.io past future width funded (Nat.div_le_self ..) size prior x.stageFloor room.signed actualFit topology
  let scale₀ := scale (J_ h) (returnRate G t f g reset)
  have scalePos : 0 < scale₀ := Nat.two_pow_pos _
  have coefficient : ratio*scale₀+1 ≤ (ratio+1)*scale₀ := by
    rw [Nat.add_mul,Nat.one_mul]; omega
  have total : x.returnInvoice room ≤ S.hostSize z.age*h*(ratio*scale₀+1)+
      S.hostSize z.age*(S.groupCount z.age*S.radix)*(ratio*scale₀) := by
    simp only [returnInvoice, PhysicalOrdinary.issuedPrefix, NativePhase.wordInvoice_seq,
      PhysicalOrdinary.signedPhase,model,base,entry,prior,oldSources,z,scale₀] at receipt ⊢
    exact receipt
  exact total.trans (Nat.add_le_add (Nat.mul_le_mul_left _ coefficient)
    (Nat.mul_le_mul_left _ ((Nat.le_add_right ..).trans coefficient)))

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
