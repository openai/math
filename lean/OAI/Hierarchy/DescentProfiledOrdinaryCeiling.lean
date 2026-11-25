import OAI.Hierarchy.DescentProfiledOrdinaryBookRooms
import OAI.Hierarchy.DescentRegisteredProfileExtent
import OAI.Hierarchy.DescentMatcherCensusRoom
import OAI.Hierarchy.DescentDatedFiniteRooms

namespace OAI
/-! # The profile, ordinary matcher and final registered shelves on one offered cut -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentSIMDLookup DescentPacking.PackedMatch DescentPacking.PackedMatch.Local.Stage Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg =>stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "face_" =>fun h (x:idx h)=>x.model

def preliminary (h : ℕ) (x:idx h) :=
  x.model.profileRepack.endAddress 0+x.model.area.rotationEnd x.model.old 0+x.model.area.donorWords+
    2^x.model.countBits+x.model.area.batch

theorem preliminary_rate (den : 0<B) :
    Bounded (preliminary G board op t f g reset τ drift degreeMax B) :=by
  let q (h) (x:idx h) := (S_ h x).censusBits x.slot.p≤2^(k_ h)
  have ready : ∀ᶠ h:ℕ in atTop,∀x:idx h,q h x:=(census_board_room G t f g reset B den).mono
    fun h ok x=>ok _ _ _ x.slot.grainLimit
  apply Bounded.of_restrict q ready
  let sample (h:ℕ):= {x:idx h // q h x}
  let a (h) (x:sample h) := x.val.model.area
  let count (h) (x:sample h):=x.val.slot.menu.seats x.val.slot.age
  let date (h) (x:sample h):=DonorDate.atDate G (S_ h x.val) g (k_ h) x.val.slot.age x.val.slot.p
  let measured (h) (x:sample h):=(date h x).schedule h (count h x) ((S_ h x.val).censusBits x.val.slot.p)
  have same : a=measured:=by
    funext h x
    exact congrArg PhysicalOrdinary.StaticCore.area x.val.core
  have geom:=PhysicalOrdinary.ordinary_geometry G t f g reset τ B
    (fun h (x:sample h)=>x.val.slot.sites) (fun h x=>x.val.slot.age) (fun h x=>x.val.slot.p)
    ((site_bound G board op t f g reset τ drift degreeMax B).restrict q) (fun _ x=>x.val.slot.active.le)
  obtain ⟨raw,lookup⟩:=PhysicalOrdinary.OrdinaryGeometry.matcher G t f g reset τ B _ _ _ geom count (fun _ x=>x.val.seats) (fun _ x=>x.property)
  have area : Dated.Ordinary.ScalarRoom a:=same.symm ▸ raw
  have six : ∀h (x:sample h),SixBirths.unit (a h x).shapeAt≤(a h x).unit:=by
    rw [same]
    exact lookup
  have profile:=PhysicalOrdinary.profile_extent_room G measured count (geom.batch.of_le (fun _ x=>x.val.seats))
    (fun _ _=>rfl) (fun _ _=>rfl) lookup
  have pl: Bounded (fun h (x:sample h)=>x.val.model.profileRepack.endAddress 0):=ProfileRepack.extent_rate _ profile
  have move:=Dated.Ordinary.rotation_rate a (fun h (x:sample h)=>x.val.model.old) area six
  have donors:=Dated.Ordinary.donor_width_rate a area
  have payload (h : ℕ) (x : sample h) : (a h x).payload=h := by
    rw [same]
    rfl
  have word (h) (x:sample h) : (a h x).unit*(a h x).lanesAt≤h/2 :=by
    have actual:=lanes_fit (a h x).payload (a h x).unit
    calc
      _ ≤ (a h x).payload / 2 := by
        simpa only [Dated.Ordinary.lanesAt,Nat.mul_comm (a h x).unit] using actual
      _ = h/2 := by rw [payload h x]
  have counter : Bounded (fun h (x:sample h)=>2^x.val.model.countBits):=by
    apply Bounded.pow_of_linear (K:=1)
    apply Eventually.of_forall
    intro h x
    have field : (a h x).shapeAt.outputBits≤SixBirths.unit (a h x).shapeAt:=
      (Nat.le_add_left ..).trans (Nat.le_max_left ..)
    rw [Nat.one_mul]
    change (a h x).shapeAt.outputBits * (a h x).lanesAt ≤ h
    exact ((Nat.mul_le_mul_right (a h x).lanesAt
      (field.trans (six h x))).trans (word h x)).trans (Nat.div_le_self ..)
  have ambient : Bounded (fun h (_:sample h)=>h):=
    ⟨1,Eventually.of_forall fun h x=>by simpa only [one_mul] using (Nat.lt_two_pow_self (n:=h)).le⟩
  have lanes : Bounded (fun h (x:sample h)=>(a h x).lanesAt):=ambient.of_le fun _ _=>Nat.div_le_self ..
  have rows : Bounded (fun h (x:sample h)=>chunks (a h x).G (a h x).lanesAt):=
    (area.groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have batch : Bounded (fun h (x:sample h)=>(a h x).batch):=by
    simpa only [Dated.Ordinary.batch,Nat.pow_succ] using
      (((area.radix.mul (Bounded.const 2)).mul area.hosts).mul rows)
  exact (((pl.add move).add donors).add counter).add batch

theorem ceiling_from_reference (den : 0<B) (slack : SignedStage.unitRate G t f g reset<B) (tailRoom:τ≤B)
    (ref : Bounded (fun h (x:idx h)=>x.model.referenceWords)) :
    Bounded (fun h (x:idx h)=>x.model.fullCeiling) :=by
  let rooms:=operand_room G board op t f g reset τ drift degreeMax B den
  obtain ⟨metadata,digits⟩:=metadata_room G board op t f g reset τ drift degreeMax B den
  have earlier:=preliminary_rate G board op t f g reset τ drift degreeMax B den
  have vec:=DescentOperandVectorArena.Layout.extent_rate _ rooms.vector
  have resolved:=DescentDatedPriorOperand.Layout.extent_rate _ rooms.resolver
  have kept:=MetadataReturn.ordinary_rate _ metadata digits
  have survivors:=(survivor_cost G board op t f g reset τ drift degreeMax B slack tailRoom).2
  have raster:=StageVenueTail.OrdinaryRaster.extent_rate _ _ _ (raster_room G board op t f g reset τ drift degreeMax B den)
  have venue:=StageVenueTail.Date.extent_rate _ (venue_room G board op t f g reset τ drift degreeMax B slack tailRoom)
  have finalBook:=DescentOrdinaryFinal.Chart.extent_rate _ rooms.finalBook
  have prim:=PhysicalOrdinary.primitive_rate (face_) (primitive_room G board op t f g reset τ drift degreeMax B den)
  apply ((((((((((earlier.add vec).add resolved).add kept).add survivors).add ref).add raster).add venue).add finalBook).add prim).add (Bounded.const 1)).of_le
  intro h x
  simp only [PhysicalOrdinary.fullCeiling,PhysicalOrdinary.returnedCeiling,PhysicalOrdinary.ceiling,
    PhysicalOrdinary.argumentExtra,Dated.Ordinary.ordinaryWords,preliminary]
  omega

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
