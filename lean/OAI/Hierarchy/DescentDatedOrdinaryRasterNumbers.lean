import OAI.Hierarchy.DescentReachedCountRepackSpace
import OAI.Hierarchy.DescentOrdinaryRasterReturn
import OAI.Hierarchy.DescentPaidSweepLayout
import OAI.Hierarchy.DescentOrdinaryShapeSlots
import OAI.Hierarchy.DescentDatedOrdinaryDimensions
import OAI.Hierarchy.DescentStageVenueDate

namespace OAI
/-! # Space for the measured ordinary paid and occupied sites in the next host order -/
namespace Hierarchy.DescentSixParty.StageVenueTail.OrdinaryRaster
open DescentPacking.PackedMatch.Local.Stage.Dated DescentPaidResidentCount DescentVenueQuantityPlanes
open DescentDatedAddressBook DescentSIMDLookup Filter
noncomputable section
variable (a:Ordinary)(d:Date)(working:ℕ)
def shapes:=(2^(a.k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots a.D
def paths:=(a.D+1)^4
def raw:=2^(a.k+1)*DescentOrdinaryVenueReturn.shapeSlots a.D
def donors:=paths a*2^a.k
def nameBits:=Nat.clog 2 (shapes a+1)
def dims:Dims:=⟨shapes a,a.H,d.hosts,d.groups,2^a.k,d.paidBits,working,d.paidLanes⟩
def prepared (base:ℕ):=(DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch.count a.H a.G a.lanesAt working a.k (paths a) d.paidBits base).roof
def sweep (base:ℕ):=Sweep.roof (prepared a d working base) (shapes a) (donors a) a.cap d.paidBits (nameBits a) a.H a.G working
def roof (base:ℕ):=DescentOrdinaryRasterReturn.roof (dims a d working) (sweep a d working base)

theorem translated (base:ℕ):roof a d working base=base+roof a d working 0:=by
  have early:prepared a d working base=base+prepared a d working 0:=DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch.translate ..
  unfold roof sweep
  rw [DescentOrdinaryRasterReturn.translated _ (Sweep.roof (prepared a d working base) ..),
    Sweep.roof_affine (prepared a d working base),early,DescentOrdinaryRasterReturn.translated _ (Sweep.roof (prepared a d working 0) ..),Sweep.roof_affine (prepared a d working 0)]
  omega

variable {ι:ℕ→Type*}
structure ScalarRoom (a:∀h,ι h→Ordinary)(d:∀h,ι h→Date)(work:∀h,ι h→ℕ):Prop where
  original:Bounded (fun h i=>(a h i).lanesAt)
  originalBits:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(d h i).paidBits*(a h i).lanesAt≤C*h
  raster:DescentOrdinaryRasterReturn.ScalarRoom (fun h i=>dims (a h i) (d h i) (work h i))
  paths:Bounded (fun h i=>paths (a h i))
  priorGroups:Bounded (fun h i=>(a h i).G)
  maskBits:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,let o:=a h i
    Sweep.maskBits (donors o) o.cap (nameBits o) (work h i)≤C*h
  sumBits:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,let o:=a h i
    Sweep.sumBits (donors o) o.cap (d h i).paidBits (work h i)≤C*h

theorem extent_rate (a:∀h,ι h→Ordinary)(d:∀h,ι h→Date)(work:∀h,ι h→ℕ)(r:ScalarRoom a d work):
    Bounded (fun h i=>roof (a h i) (d h i) (work h i) 0):=by
  have p:=r.raster.full.sheets
  have H:=r.raster.full.oldHosts
  have M:=r.raster.full.oldLanes
  have rest:=DescentOrdinaryRasterReturn.extent_rate _ r.raster
  obtain ⟨C,hC⟩:=r.maskBits
  obtain ⟨T,hT⟩:=r.sumBits
  have mask:=Bounded.pow_of_linear (K:=C) hC
  have fee:=Bounded.pow_of_linear (K:=T) hT
  have chunk:Bounded (fun h i=>chunks (a h i).G (work h i)):=
    (r.priorGroups.add M).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have temp:=((p.mul (Bounded.const 2)).mul mask)
  have span:=(p.mul (H.mul chunk)).padded
  have earlier:=DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch.roof_rate
    (fun h i=>(a h i).H) (fun h i=>(a h i).G) (fun h i=>(a h i).lanesAt) work
    (fun h i=>(a h i).k) (fun h i=>paths (a h i)) (fun h i=>(d h i).paidBits)
    (fun h i=>(a h i).cap) H r.priorGroups r.original M r.raster.full.blocks r.paths
    (fun _ _=>pow_pos (Nat.succ_pos _) 4) r.originalBits r.sumBits
  apply (earlier.add (((((temp.add ((Bounded.const 2).mul fee)).add span).add temp).add span).add rest)).of_le
  intro h i
  rw [roof,DescentOrdinaryRasterReturn.translated,sweep,Sweep.roof_affine (prepared _ _ _ 0)]
  simp only [Sweep.roof,Sweep.aliveBank,Sweep.actorBase,Sweep.paidBank,Sweep.sumBase,Sweep.span,
    Sweep.rowCount,dims,prepared,Nat.zero_add,Nat.add_assoc]
  exact Nat.le_refl _

end
end Hierarchy.DescentSixParty.StageVenueTail.OrdinaryRaster

end OAI
