import OAI.Hierarchy.DescentFundedRasterRowFee
import OAI.Hierarchy.DescentNamedArgumentVolume
import OAI.Hierarchy.DescentProfiledOrdinaryOffer

namespace OAI
/-! # The clipped-raster invoice on an attained chronological offer -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook Chronology Chronology.RegisterTimeline
open DescentInitialHost DescentResetInvoice DescentPacking.PackedMatch.Local.Stage DescentMixedRouter Filter
open ThreeFlat.Routing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
    (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg =>Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg=>stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))
local notation "k_" h:arg=>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "port_" x:arg=>(x).slot.position.ports

/-- The exponent uses only the fixed gadget and scheduling rates. The buses,
local degree, chosen pitches, and public prefix can vary over all offers. -/
def fundedRasterExponent (driftR : ℕ) :=
  24*(20+44*argumentDigitRate G t f g reset driftR (NativePitch.FundedBase.public_rate G t f g reset).choose)

theorem funded_raster_rows {h : ℕ} (x : idx h) (driftR ratio : ℕ)
    (grant : ArgumentCalendar G op t f g reset τ B drift driftR degreeMax h)
    (dr : drift+1≤ scale (J_ h) driftR) (positive : 0<(S_ h x).hostSize x.slot.age) :
    let e:=x.base.argumentUnitFrom (port_ x) x.stageFloor
    x.model.fundedFee h (4*x.base.area.unit) (x.base.fundedWorkingUnit e)
      (2^(k_ h)*x.base.fundedWorkingUnit e) 7 ratio≤
      ratio*scale (J_ h) (fundedRasterExponent G t f g reset driftR)*x.model.rowVolume h :=by
  intro e
  let S:=S_ h x
  let J:=J_ h
  let P:=port_ x
  let c:=x.cut
  let m:=x.slot.menu
  let base:=(NativePitch.FundedBase.public_rate G t f g reset).choose
  let localR:=argumentDigitRate G t f g reset driftR base
  let a:=20+44*localR
  let U:=scale J a
  have smaller {r : ℕ} (h : r≤a) : scale J r≤U :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h)
  have large : 8192≤U:=by
    have count : 8192 ≤ scale J 13 := by
      change (2:ℕ)^13 ≤ 2^(13*(J+1))
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 13 (Nat.succ_pos J))
    exact count.trans (smaller (by dsimp only [a];omega))
  have history := x.slot.geometry.room.archive
  have oldNodes : P.nodes≤S.retainedNodes := by
    rw [history.nodes]
    split
    · change 1≤(2^S.height)^S.localTokenExponent
      exact pow_pos (Nat.two_pow_pos S.height) S.localTokenExponent
    · exact le_rfl
  have oldSlots : P.argumentsPerNode≤S.retainedArgumentsAt G drift:=x.slot.geometry.room.args
  have oldBits : P.operandBits=DescentOperandWidth.recordBits G S (k_ h) (tail τ J) drift x.slot.degree x.slot.p :=
    history.digits
  have charts:=grant.book x.slot.sites x.slot.age x.slot.p x.slot.degree (m.seats x.slot.age) P
  have sizes (j : _) : x.books.bookMouthParameters j≤U:=
    ((charts x.slot.grainLimit x.slot.degreeLimit oldNodes oldSlots dr) j).trans (smaller (by
      dsimp only [localR,base,a,argumentDigitRate]
      omega))
  have initial:=Branch.registered_base_width c.original G S c.branch c.ticket c.before c.after c.joined
    op (tail τ J) drift x.slot.degree h (m.seats x.slot.age) P.venue.lanes P P.io.roster m.ordinary
    grant rfl rfl x.slot.grainLimit
  have chosen:=Branch.registered_width_at c.original G S c.branch c.ticket c.before c.after c.joined
    op (tail τ J) drift x.slot.degree h (m.seats x.slot.age) P.venue.lanes P P.io.roster m.ordinary x.stageFloor
    grant rfl rfl rfl dr initial x.slot.degreeLimit x.slot.grainLimit x.firstWidth oldNodes oldSlots oldBits
  have funds : x.base.fundedMaxUnit e≤U:=chosen.trans (smaller (by dsimp only [a,localR,base];omega))
  have date:=Branch.donor_date_eq c.original G S c.branch c.ticket c.before c.after c.joined
  have actual : c.source.placement.degree=x.books.reference.degree:=congrArg DonorDate.degree date
  have site:=P.registered_section_population c.ticket op g (tail τ J) x.slot.p f drift x.slot.degree h
    (m.seats x.slot.age) P.venue.lanes P.io.roster m.ordinary x.stageFloor (t:=t) (J:=J) (reset:=reset)
    (M:=x.slot.sites) rfl positive c.radix
  have row:=OrdinaryBooks.registered_funded_raster_rows c.ticket g (tail τ J) x.slot.p f h
    (m.seats x.slot.age) P.venue.lanes P.io.roster m.ordinary op drift x.slot.degree P x.stageFloor
    U ratio large sizes actual funds site c.radix
  have price : U^24=scale J (fundedRasterExponent G t f g reset driftR) :=by
    change (2^(a*(J+1)))^24=2^((24*a)*(J+1))
    rw [←pow_mul]
    congr 1
    ring
  exact row.trans_eq (congrArg (fun u : ℕ => ratio*u*x.model.rowVolume h) price)

/-- A single fixed exponent absorbs every occurrence after the public height threshold. -/
theorem eventual_funded_raster_rows (den : 0<B) :
    ∀ᶠ h : ℕ in atTop, ∀ (x : idx h) (ratio : ℕ), 0<(S_ h x).hostSize x.slot.age →
      let e:=x.base.argumentUnitFrom (port_ x) x.stageFloor
      x.model.fundedFee h (4*x.base.area.unit) (x.base.fundedWorkingUnit e)
        (2^(k_ h)*x.base.fundedWorkingUnit e) 7 ratio≤
        ratio*scale (J_ h) (fundedRasterExponent G t f g reset 1)*x.model.rowVolume h :=by
  filter_upwards [eventual_argument_width G op t f g reset τ B drift 1 degreeMax den,
    eventually_late (drift+1) B den] with h grant late
  have small : drift+1≤ scale (J_ h) 1 := late.trans (by
    change J_ h≤2^(1*(J_ h+1))
    rw [one_mul,pow_succ]
    have:=Nat.lt_two_pow_self (n:=J_ h)
    omega)
  exact fun x ratio pos=>funded_raster_rows G board op t f g reset τ drift degreeMax B x 1 ratio grant small pos

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
