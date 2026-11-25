import OAI.Hierarchy.DescentUniformMetadataRoom
import OAI.Hierarchy.DescentProfiledOrdinaryOffer
import OAI.Hierarchy.DescentPurchasedOrdinaryVenueRoom
import OAI.Hierarchy.DescentProfiledOrdinaryRasterRoom

namespace OAI
/-! # Operand, metadata and venue address bounds at the offered ordinary date -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage Filter
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "tb_" h:arg => tail τ (J_ h)
local notation "S_" h:arg x:arg =>stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tb_ h)
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "v_" => fun h (x:idx h)=>x.model
local notation "p_" x:arg => (x).slot.position.ports
local notation "seats_" x:arg => (x).slot.menu.seats (x).slot.age
local notation "core_" h:arg x:arg => PhysicalOrdinary.StaticCore.atAge G (S_ h x) g (k_ h) (x).slot.age (x).slot.p h (seats_ x)
    (x).slot.position.floor (p_ x).io.roster

theorem site_bound : Bounded (fun h (x:idx h)=>x.slot.sites) :=
  ⟨2,Eventually.of_forall fun h x=>by simpa only [←pow_mul,Nat.mul_comm h 2] using x.slot.siteLimit⟩

theorem geometry : PhysicalOrdinary.OrdinaryGeometry G t f g reset τ B
    (fun h (x:idx h)=>x.slot.sites) (fun _ x=>x.slot.age) (fun _ x=>x.slot.p) :=
  PhysicalOrdinary.ordinary_geometry G t f g reset τ B _ _ _ (site_bound ..) (fun _ x=>x.slot.active.le)

theorem previous_nodes (h) (x : idx h) : (p_ x).nodes≤(S_ h x).retainedNodes :=by
  rw [x.slot.geometry.room.archive.nodes]
  split
  · change 0<(2^_)^_
    positivity
  · rfl

theorem primitive_room (den : 0<B) : PhysicalOrdinary.PrimitiveScalarRoom (v_) :=
  (PhysicalOrdinary.registered_primitive_rate G op t f g reset τ B drift degreeMax _ _ _ _ _ _ _ _
    den (geometry ..) (fun _ x=>x.primitive_shape) (Eventually.of_forall fun _ x=>
      ⟨x.slot.grainLimit,x.slot.degreeLimit,previous_nodes ..,x.firstWidth⟩)).1

theorem pitch (h) (x:idx h) :
    x.model.resolver.lanes≤h ∧ (S_ h x).censusBits x.slot.p*x.model.resolver.lanes≤h/4 :=
  (PhysicalOrdinary.registered_venue_pitch x.books x.cut.ticket g (tb_ h) x.slot.p f h
    (seats_ x) (p_ x).venue.lanes (p_ x).io.roster x.slot.menu.ordinary (p_ x) x.stageFloor).2

theorem argument_bound : Bounded (fun h (x:idx h)=>x.model.vector.operands) :=by
  let e:=operandExponent G (stageNumbers G t 0 f g reset 0 0)
  have level : ∀ᶠ h:ℕ in atTop,J_ h≤h:=Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have base : SmallAt (fun h=>J_ h) (fun h (_:idx h)=>(2^(J_ h))^e) :=by
    refine ⟨e,Eventually.of_forall fun h x=>?_⟩
    change (2^(J_ h))^e ≤ 2^(e*(J_ h+1))
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by nlinarith)
  apply ((Bounded.const (drift+1)).mul (base.bounded level)).of_le
  intro h x
  change max (p_ x).argumentsPerNode ((S_ h x).retainedArgumentsAt G drift)≤(S_ h x).retainedArgumentsAt G drift
  exact max_le x.slot.geometry.room.args le_rfl

theorem operand_room (den : 0<B) : PhysicalOrdinary.OperandRooms (v_) :=by
  let prim:=primitive_room G board op t f g reset τ drift degreeMax B den
  have geo:=geometry G board op t f g reset τ drift degreeMax B
  have original:=OrdinaryBooks.primitive_date_local G op t f g reset τ B drift degreeMax den
  have nodes : SmallAt (fun h=>J_ h) (fun h (x:idx h)=>x.model.resolver.nodes) :=by
    refine ⟨OrdinaryBooks.primitiveLocalRate G t f g reset,?_⟩
    filter_upwards [original] with h saved
    exact fun x=>(saved x.slot.sites x.slot.age x.slot.p x.slot.degree (seats_ x) (p_ x)
      x.slot.grainLimit x.slot.degreeLimit (previous_nodes ..) x.firstWidth).2.2.2.1
  have level : ∀ᶠ h:ℕ in atTop,J_ h≤h:=Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have ambient : Bounded (fun h (_:idx h)=>h):=
    ⟨1,Eventually.of_forall fun h x=>by simpa only [one_mul] using (Nat.lt_two_pow_self (n:=h)).le⟩
  exact PhysicalOrdinary.operand_rooms (v_) (Eventually.of_forall fun h x=>x.prices)
    (fun h x=>x.base.registered_geometry (p_ x) x.stageFloor)
    (fun h x=>(x.base.registered_node_chart (p_ x) x.stageFloor).2) (fun _ _=>rfl)
    prim.hosts prim.lows (nodes.bounded level) (argument_bound ..) geo.blocks geo.axis.newGroup
    (ambient.of_le (fun h x=>(pitch G board op t f g reset τ drift degreeMax B h x).1))

theorem metadata_room (den : 0<B) :
    MetadataReturn.ScalarRoom (fun h (x:idx h)=>x.model.metadata) ∧
    ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀x:idx h,let m:=x.model.metadata;(m.spanBits*m.chart.nodes)*m.chart.lanes≤K*h :=
  metadata_from_resolver G board op t f g reset drift degreeMax (ι := fun h => idx h) (fun _ _ => τ)
    (fun _ _ => B) (fun _ x => x) (operand_room G board op t f g reset τ drift degreeMax B den).resolver

theorem venue_room (slack : SignedStage.unitRate G t f g reset<B) (tailRoom:τ≤B) :
    StageVenueTail.Date.ScalarRoom (fun h (x:idx h)=>x.model.venue) :=by
  let target h (x:idx h) := (OrdinaryBooks.purchaseClip G x.books (core_ h x) (p_ x)
    ((S_ h x).censusBits x.slot.p)).postPitch
  have eqn : (fun h (x:idx h)=>x.model.venue)=(fun h (x:idx h)=>
      StageVenueTail.Date.atOrdinary G (S_ h x) g (k_ h) (tb_ h) x.slot.p f h x.slot.menu.ordinary x.slot.age (target h x)) :=by
    funext h x
    have bought:=(Branch.registered_purchased_books x.cut.original G (S_ h x) x.cut.branch x.cut.ticket
      x.cut.before x.cut.after x.cut.joined op (tb_ h) drift x.slot.degree h (seats_ x) x.slot.position.floor
      (p_ x) x.slot.menu.ordinary).2
    exact congrArg (fun clip:DescentOrdinaryVenueIngress.Clip=>
      StageVenueTail.Date.atOrdinary G (S_ h x) g (k_ h) (tb_ h) x.slot.p f h x.slot.menu.ordinary x.slot.age clip.postPitch) bought
  rw [eqn]
  exact StageVenueTail.Date.purchased_venue_room_at G t f g reset τ B slack tailRoom
    _ _ _ _ _ _ _ (site_bound ..) (fun _ x=>x.slot.active) (fun _ _ _=>rfl) (fun _ _=>rfl)

theorem survivor_cost (slack : SignedStage.unitRate G t f g reset<B) (tailRoom:τ≤B) :
    MaterialExtent.ScalarRoom (fun h (x:idx h)=>x.model.material) ∧ Bounded (fun h (x:idx h)=>x.model.survivorWords) :=
  PhysicalOrdinary.ordinary_survivor_cost G (v_) t f g reset τ B _ _ _ _ _ _ _ (site_bound ..)
    (fun _ x=>x.slot.active) slack (fun _ x=>x.core) (fun _ _=>rfl)
    (fun h x=>Branch.signed_at x.cut.original G (S_ h x) x.cut.branch x.cut.ticket x.cut.before x.cut.after x.cut.joined h)
    (venue_room G board op t f g reset τ drift degreeMax B slack tailRoom).degree

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
