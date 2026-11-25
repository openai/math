import OAI.Hierarchy.DescentDatedOrdinaryPrimitiveRate
import OAI.Hierarchy.DescentDatedOrdinaryMaterial
import OAI.Hierarchy.DescentDatedOrdinaryRasterExtent
import OAI.Hierarchy.DescentOrdinaryFinalRate
import OAI.Hierarchy.DescentDatedVenueRate
import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentOrdinaryCountScan
import OAI.Hierarchy.DescentOrdinaryVenueExtent

namespace OAI
/-! # The real dated ordinary selector reads the final prefix of issued pairs -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch DescentSIMDLookup DescentPackedColony Filter
open ThreeFlat.Routing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
def stageStart (floor : ℕ) :=v.profileRepack.endAddress floor
def rasterEnd (floor : ℕ) :=StageVenueTail.OrdinaryRaster.roof v.area v.venue v.rasterLanes (v.endAddress floor)
def venueEnd (floor : ℕ) :=v.venue.endAddress (v.rasterEnd floor)
def metaStart (floor : ℕ) :=v.venueEnd floor
def metaEnd (floor : ℕ) :=v.metadata.ordinaryEnd (v.metaStart floor)
def operandEnd (floor : ℕ) :=v.operandBook.endAddress (v.metaEnd floor)
def primitiveEnd (floor : ℕ) :=v.primitiveRoof (v.operandEnd floor)
def countBits :=v.area.shapeAt.outputBits*v.area.lanesAt
def countAddr (floor : ℕ) :=DescentOrdinaryCountScan.address v.countBits (v.primitiveEnd (v.stageStart floor)) v.area.batch
def returnedEnd (floor : ℕ) :=DescentOrdinaryCountScan.endAddress v.countBits (v.primitiveEnd floor) v.area.batch
def fullEnd (floor : ℕ) :=v.returnedEnd (v.stageStart floor)
def returnedCeiling  := v.ceiling+StageVenueTail.OrdinaryRaster.roof v.area v.venue v.rasterLanes 0+v.venue.endAddress 0+v.metadata.ordinaryEnd 0+v.operandBook.endAddress 0+v.primitiveRoof 0+2^v.countBits+v.area.batch+1

def fullCeiling :=v.profileRepack.endAddress 0+v.returnedCeiling

theorem count_written (floor : ℕ) : v.countAddr floor+1=v.fullEnd floor :=rfl

theorem returned_spent (floor : ℕ) :
    floor≤v.returnedEnd floor ∧ v.returnedEnd floor≤floor+v.returnedCeiling ∧ v.returnedEnd floor=floor+v.returnedEnd 0 :=by
  obtain ⟨start,cap,shift⟩:=v.spent floor
  have pagePos:=Nat.two_pow_pos v.countBits
  simp only [returnedEnd,returnedCeiling,DescentOrdinaryCountScan.endAddress,DescentOrdinaryCountScan.out,primitiveEnd]
  rw [(v.primitive_spent (v.operandEnd floor)).1,(v.primitive_spent (v.operandEnd 0)).1]
  simp only [operandEnd]
  rw [v.operandBook.affine (v.metaEnd floor),v.operandBook.affine (v.metaEnd 0)]
  simp only [metaEnd]
  rw [v.metadata.ordinary_translate (v.metaStart floor),v.metadata.ordinary_translate (v.metaStart 0)]
  simp only [metaStart,venueEnd]
  rw [v.venue.translates (v.rasterEnd floor),v.venue.translates (v.rasterEnd 0)]
  simp only [rasterEnd]
  rw [StageVenueTail.OrdinaryRaster.translated _ _ _ (v.endAddress floor),
    StageVenueTail.OrdinaryRaster.translated _ _ _ (v.endAddress 0)]
  omega

theorem full_spent (floor : ℕ) :
    floor≤v.fullEnd floor ∧ v.fullEnd floor≤floor+v.fullCeiling ∧ v.fullEnd floor=floor+v.fullEnd 0 :=by
  have here:=v.returned_spent (v.stageStart floor)
  have zero:=v.returned_spent (v.stageStart 0)
  have start : v.stageStart floor=floor+v.stageStart 0:=v.profileRepack.translate floor
  have same : v.profileRepack.endAddress 0=v.stageStart 0 := rfl
  unfold fullEnd fullCeiling
  omega

theorem cover_after_survivors {ι : ℕ→Type*} {Pins : ∀h,ι h→Type} (v : ∀h (i:ι h),PhysicalOrdinary F (Pins h i))
    (b : Local.Stage.Dated.Ordinary.ScalarRoom (fun h i=>(v h i).area))
    (six : ∀h i,SixBirths.unit (v h i).area.shapeAt≤(v h i).unit)
    (vector : DescentOperandVectorArena.Layout.ScalarRoom (fun h i=>(v h i).vector))
    (resolved : DescentDatedPriorOperand.Layout.ScalarRoom (fun h i=>(v h i).resolver))
    (profile : ProfileRepack.ScalarRoom (fun h i=>(v h i).profileRepack))
    (metadata : MetadataReturn.ScalarRoom (fun h i=>(v h i).metadata))
    (digits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let m:=(v h i).metadata;(m.spanBits*m.chart.nodes)*m.chart.lanes≤K*h)
    (book : DescentOrdinaryFinal.Chart.ScalarRoom (fun h i=>(v h i).operandBook))
    (extra:Bounded (fun h i=>(v h i).referenceWords))
    (survivors : Bounded (fun h i=>(v h i).survivorWords))
    (raw:StageVenueTail.OrdinaryRaster.ScalarRoom (fun h i=>(v h i).area) (fun h i=>(v h i).venue) (fun h i=>(v h i).rasterLanes))
    (venue : DescentSixParty.StageVenueTail.Date.ScalarRoom (fun h i=>(v h i).venue))
    (primitive : PrimitiveScalarRoom v) :
    Bounded (fun h i=>(v h i).fullCeiling) :=by
  have pl:=ProfileRepack.extent_rate _ profile
  have prev : Bounded (fun h i=>(v h i).ceiling) :=
    (((Local.Stage.Dated.Ordinary.ordinary_words_rate _ _ _ b six vector).add (survivors.add extra)).add
      (DescentDatedPriorOperand.Layout.extent_rate _ resolved))
  have kept:=MetadataReturn.ordinary_rate _ metadata digits
  have roles:=primitive_rate v primitive
  have written:=DescentOrdinaryFinal.Chart.extent_rate _ book
  have rasters:=StageVenueTail.OrdinaryRaster.extent_rate _ _ _ raw
  have entry:=DescentSixParty.StageVenueTail.Date.extent_rate _ venue
  obtain ⟨C,hc⟩:=b.payload
  have page : Bounded (fun h i=>2^(v h i).countBits) :=by
    apply Bounded.pow_of_linear (K:=C)
    filter_upwards [hc] with h high
    intro i
    let a:=(v h i).area
    have field : a.shapeAt.outputBits≤SixBirths.unit a.shapeAt :=
      (Nat.le_add_left ..).trans (Nat.le_max_left ..)
    have word : a.unit*a.lanesAt≤a.payload/2 :=by
      simpa only [Local.Stage.Dated.Ordinary.lanesAt,Nat.mul_comm a.unit] using lanes_fit a.payload a.unit
    exact ((Nat.mul_le_mul_right a.lanesAt (field.trans (six h i))).trans word).trans ((Nat.div_le_self ..).trans (high i))
  have payload : Bounded (fun h i=>(v h i).area.payload) :=by
    refine ⟨C,?_⟩
    exact hc.mono fun h high i=>(high i).trans (Nat.lt_two_pow_self.le)
  have batch : Bounded (fun h i=>(v h i).area.batch) :=by
    have lanes : Bounded (fun h i=>(v h i).area.lanesAt) :=payload.of_le fun _ _=>Nat.div_le_self ..
    have rows : Bounded (fun h i=>chunks (v h i).area.G (v h i).area.lanesAt) :=
      (b.groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
    simpa only [Local.Stage.Dated.Ordinary.batch,Nat.pow_succ] using
      (((b.radix.mul (Bounded.const 2)).mul b.hosts).mul rows)
  apply pl.add
  exact (((((((prev.add rasters).add entry).add kept).add written).add roles).add page).add batch).add (Bounded.const 1)

theorem cover_rate {ι : ℕ→Type*} {Pins : ∀h,ι h→Type} (v : ∀h (i:ι h),PhysicalOrdinary F (Pins h i))
    (b : Local.Stage.Dated.Ordinary.ScalarRoom (fun h i=>(v h i).area))
    (six : ∀h i,SixBirths.unit (v h i).area.shapeAt≤(v h i).unit)
    (vector : DescentOperandVectorArena.Layout.ScalarRoom (fun h i=>(v h i).vector))
    (resolved : DescentDatedPriorOperand.Layout.ScalarRoom (fun h i=>(v h i).resolver))
    (profile : ProfileRepack.ScalarRoom (fun h i=>(v h i).profileRepack))
    (metadata : MetadataReturn.ScalarRoom (fun h i=>(v h i).metadata))
    (digits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let m:=(v h i).metadata;(m.spanBits*m.chart.nodes)*m.chart.lanes≤K*h)
    (book : DescentOrdinaryFinal.Chart.ScalarRoom (fun h i=>(v h i).operandBook))
    (extra:Bounded (fun h i=>(v h i).referenceWords))
    (reverse:Bounded (fun h i=>(v h i).reverseWords))
    (routing:MaterialExtent.ScalarRoom (fun h i=>(v h i).material))
    (marks:DescentOrdinaryMarkProject.Shape.ScalarRoom (fun h i=>(v h i).markShape))
    (signed : SignedExtent.ScalarRoom (fun h i=>(v h i).signed))
    (raw:StageVenueTail.OrdinaryRaster.ScalarRoom (fun h i=>(v h i).area) (fun h i=>(v h i).venue) (fun h i=>(v h i).rasterLanes))
    (venue : DescentSixParty.StageVenueTail.Date.ScalarRoom (fun h i=>(v h i).venue))
    (primitive : PrimitiveScalarRoom v) :
    Bounded (fun h i=>(v h i).fullCeiling) :=by
  have peers:=DescentOrdinaryVenueReturn.rate b.hosts b.degree venue.hosts venue.degree
  have survivors:=((((reverse.add (MaterialExtent.extent_rate _ routing)).add peers).add
    (DescentOrdinaryMarkProject.Shape.extent_rate _ marks)).add (SignedExtent.rate _ signed))
  exact cover_after_survivors v b six vector resolved profile metadata digits book extra survivors raw venue primitive

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
