import OAI.Hierarchy.DescentProfiledOrdinaryOffer
import OAI.Hierarchy.DescentNamedDonorPhysicalRoof
import OAI.Hierarchy.DescentMatcherRoomCalendar
import OAI.Hierarchy.DescentPrivateDonorPopulation
import OAI.Hierarchy.DescentOrdinaryChargeArithmetic

namespace OAI
namespace Hierarchy.DescentSixParty.SeedNamed.OrdinaryCut
open DescentCompiler DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage
open Chronology DescentMixedRouter DescentResetInvoice DescentDatedAddressBook ThreeFlat.Routing
noncomputable section

private theorem privatePairPaid {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
    {k i p f g : ℕ} (c : OrdinaryCut G S k i p f g) {t J reset M frozen : ℕ}
    (schedule : S = stageNumbers G t J f g reset M frozen)
    (depth : k = groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (payload seats board floor header w ratio : ℕ) (input : Dated.Operands) :
    let date := DonorDate.atDate G S g k i p
    let base := (date.schedule payload seats board).rotationEnd input.roster floor
    let r := donorRates G t f g reset
    let short := max (k+3) (Nat.clog 2 (c.source.placement.degree+1))
    let prof := DescentTerminalEpochBits.width G.C
    header ≤ base → 0 < c.ticket.installedDonorWidth short prof →
      2 * c.ticket.installedDonorWidth short prof ≤ payload → payload ≤ w → w ≤ ratio*payload →
      c.ticket.wholeDonorEnd short prof (hostRows (S.hostSize i)) payload base ≤ 2^w →
      0 < S.hostSize i → 2^(payload/2) ≤ S.hostSize i →
      ProtocolRAMPortScale.bitWidth (S.grainAt G.b p i) ≤ S.hostSize i →
      (date.afterMatcher payload seats input board floor w).wordInvoice +
        DateBill.bitTariff ((date.counter payload base header).program w) (date.counter payload base header).ticks ≤
        S.hostSize i*payload*(7*(2*ratio)*(1274+6*scale J r.work))+
          S.hostSize i*(S.groupCount i*S.radix)*(7*(2*ratio)*(4*scale J r.amount*(342+2*scale J r.work))) := by
  rcases c with ⟨_, _, X, _, _, _, _, _, _, _, _, _, br, _, _, _, _, rate, stage, _, _, _, _, _, _,
    ticket, before, after, joined⟩
  obtain rfl := ticket.sourceRate
  obtain rfl := eq_of_heq ticket.placement
  exact Branch.private_pair_paid X G S br ticket before after joined schedule depth payload seats board
    floor header w ratio input

end
end Hierarchy.DescentSixParty.SeedNamed.OrdinaryCut

/-! # Per-date private accounting for the accumulated low donor field and its public meter -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentResetInvoice Chronology
open Chronology.RegisterTimeline DescentPacking.PackedMatch.Local.Stage DescentDatedAddressBook DescentPackedProfileInstall
open DescentMixedRouter Filter
open ThreeFlat.Routing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
  (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg=>ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg=>Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg=>stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))
local notation "k_" h:arg=>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "shelf_" x:arg=>(x).slot.menu.profile (x).slot.age
local notation "seats_" x:arg=>(x).slot.menu.seats (x).slot.age


def privateDonorRate :=(donorRates G t f g reset).amount+(donorRates G t f g reset).work
def privateDonorLead (ratio : ℕ) := 40000*ratio
local notation "date_" h:arg x:arg=>DonorDate.atDate G (S_ h x) g (k_ h) (x).slot.age (x).slot.p
local notation "area_" h:arg x:arg=>(date_ h x).schedule h (seats_ x) ((S_ h x).censusBits (x).slot.p)
local notation "rot_" h:arg x:arg=>(area_ h x).rotationEnd (x).slot.position.ports.io.roster (x).stageFloor
local notation "profileCut_" x:arg=>(x).slot.position.floor
local notation "board_" h:arg x:arg=>(S_ h x).censusBits (x).slot.p

attribute [local irreducible] DonorDate.afterMatcher DonorDate.counter NativePhase.wordInvoice
set_option maxHeartbeats 800000 in
theorem eventual_donor_rows (den : 0 < B)
    (headroom : 2*((2+hostRate t reset*(t+1)+
      ((donorRates G t f g reset).amount+(donorRates G t f g reset).work)+1+1)+5+0) ≤ B) :
    ∀ᶠ h : ℕ in atTop, ∀(x : idx h) (ratio w : ℕ), 2^h ≤ x.slot.sites → h ≤ w → w ≤ ratio*h →
      x.slot.menu.header ≤ x.slot.position.floor → x.model.endAddress x.stageFloor<2^w →
      let m : Dated.Meter := (date_ h x).counter h (rot_ h x) x.slot.menu.header
      let H:=(S_ h x).hostSize x.slot.age
      let K:=(S_ h x).groupCount x.slot.age*(S_ h x).radix
      let c:=privateDonorLead ratio*scale (J_ h) (privateDonorRate G t f g reset)
      NativePhase.wordInvoice (w:=w) ((date_ h x).afterMatcher h (seats_ x) x.slot.position.ports.io (board_ h x) x.stageFloor w)+
        DateBill.bitTariff (m.program w) m.ticks ≤ H*h*c+H*K*c :=by
  filter_upwards [matcher_room_at G t f g reset 0 τ B den headroom,NativeBranch.dates_grain_room G t f g reset τ B]
    with h available grains
  intro x ratio w source hw bus header limit m H K c
  let S:=S_ h x
  let J:=J_ h
  let days:=donorRates G t f g reset
  let r:=x.cut
  let z:=x.slot
  let src:=z.position.ports
  let b:=area_ h x
  have enough : 2^h ≤ 2*z.sites:=by change 2^h ≤ 2*x.slot.sites;omega
  have inc:=available z.sites z.p enough z.grainLimit
  have small:=inc.packed r.ticket
  have sizes:=grains z.sites z.p z.age enough z.grainLimit
  have rootOrder : z.menu.header ≤ x.stageFloor:=by
    have move : x.base.stageStart z.position.floor=z.position.floor+x.base.stageStart 0:=
      x.base.profileRepack.translate z.position.floor
    change z.menu.header ≤ x.base.stageStart z.position.floor
    rw [move];exact header.trans (Nat.le_add_right ..)
  have past : z.menu.header ≤ rot_ h x:=by
    have add:=b.rotation_add src.io.roster 0 x.stageFloor
    simp only [Nat.add_zero] at add
    rw [show rot_ h x = x.stageFloor+b.rotationEnd src.io.roster 0 from add];exact rootOrder.trans (Nat.le_add_right ..)
  have extent:=Branch.installed_donor_roof r.original G S r.branch r.ticket r.before r.after r.joined op
    (tail τ J) drift z.degree h (seats_ x) z.position.floor src z.menu.ordinary
  have roofBound : r.ticket.wholeDonorEnd
      (max ((k_ h)+3) (Nat.clog 2 (r.source.placement.degree+1)))
      (DescentTerminalEpochBits.width G.C) (hostRows (S.hostSize z.age)) h (rot_ h x) ≤ 2^w :=
    Nat.le_trans extent (Nat.le_of_lt limit)
  have paid:=OrdinaryCut.privatePairPaid r (J:=J)
    (t:=t) (reset:=reset) (M:=z.sites) (frozen:=tail τ J) rfl rfl h (seats_ x) (S.censusBits z.p)
    x.stageFloor z.menu.header w ratio src.io past small.1 small.2 hw bus roofBound
    sizes.1 sizes.2.1 sizes.2.2
  let A:=scale J days.amount
  let B₀:=scale J days.work
  have posA : 1 ≤ A:=Nat.one_le_two_pow
  have posB : 1 ≤ B₀:=Nat.one_le_two_pow
  have product : scale J (privateDonorRate G t f g reset)=A*B₀:=by
    dsimp only [privateDonorRate,A,B₀,days,scale];rw [Nat.add_mul,pow_add]
  suffices upper :
      7*(2*ratio)*(1274+6*B₀) ≤ c ∧ 7*(2*ratio)*(4*A*(342+2*B₀)) ≤ c by
    exact paid.trans (Nat.add_le_add (Nat.mul_le_mul_left _ upper.1) (Nat.mul_le_mul_left _ upper.2))
  dsimp only [c,privateDonorLead];rw [product]
  exact private_coefficients A B₀ ratio posA posB

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
