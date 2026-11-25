import OAI.Hierarchy.DescentDatedOverlapAperture

namespace OAI
/-! Dated addresses for the original donor observations and their projected receiver fields. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup Filter
noncomputable section
structure MaterialExtent where
  oldHosts : ℕ
  oldGroups : ℕ
  oldLanes : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  blocks : ℕ
  reach : ℕ
  oldSlots : ℕ
  jointBits : ℕ
  fieldBits : ℕ
namespace MaterialExtent
variable (s : MaterialExtent)
def sourceRows := s.oldHosts*chunks s.oldGroups s.oldLanes
def nextRows := s.hosts*chunks s.groups s.lanes
def seats := s.blocks*s.oldSlots*11
def fields := 15*s.seats
def keyBits := s.jointBits*s.oldLanes
def socketBits := (s.fieldBits*s.blocks+s.fieldBits)*s.lanes
def chartWords :=s.sourceRows+(s.sourceRows+s.reach*((s.oldLanes+1)*(s.reach+1)))
def chartStep := (s.oldLanes+1)*(s.reach+1)
def chartGuard := ((s.chartWords+2^Nat.clog 2 s.sourceRows)+2^Nat.clog 2 s.chartStep)+2^Nat.clog 2 (s.oldHosts*s.reach)
def joinBase (base : ℕ) :=base+s.chartGuard
def jointStart (base : ℕ) :=s.joinBase base+2*2^s.keyBits
def observationsStart (base : ℕ) :=s.jointStart base+2^Nat.clog 2 (s.sourceRows+1)
def pageWords :=2^s.keyBits+2^Nat.clog 2 s.sourceRows
def valuesStart (base : ℕ) :=s.observationsStart base+s.fields*s.pageWords
def overlapStart (base : ℕ) :=s.valuesStart base+2^Nat.clog 2 (s.fields*s.sourceRows+1)
def projectionStart (base : ℕ) :=
  Overlap.endAddress (s.overlapStart base) (s.fields*s.oldHosts) s.oldGroups s.oldLanes (s.lanes*s.blocks) s.fieldBits
def mapsStart (base : ℕ) :=s.projectionStart base+(4*s.blocks)*2^s.socketBits
def endAddress (base : ℕ) :=s.mapsStart base+(s.reach+2)*2^Nat.clog 2 (s.nextRows+1)

theorem translated (base : ℕ) : s.endAddress base=base+s.endAddress 0 :=by
  unfold endAddress mapsStart projectionStart
  rw [Overlap.address_affine (s.overlapStart base),Overlap.address_affine (s.overlapStart 0)]
  simp only [overlapStart,valuesStart,observationsStart,jointStart,joinBase,Nat.zero_add,Nat.add_assoc]

variable {ι : ℕ→Type*} (s : ∀h,ι h→MaterialExtent)
structure ScalarRoom : Prop where
  oldHosts : Bounded (fun h i=>(s h i).oldHosts)
  oldGroups : Bounded (fun h i=>(s h i).oldGroups)
  oldLanes : Bounded (fun h i=>(s h i).oldLanes)
  hosts : Bounded (fun h i=>(s h i).hosts)
  groups : Bounded (fun h i=>(s h i).groups)
  lanes : Bounded (fun h i=>(s h i).lanes)
  blocks : Bounded (fun h i=>(s h i).blocks)
  reach : Bounded (fun h i=>(s h i).reach)
  oldSlots : Bounded (fun h i=>(s h i).oldSlots)
  joinRoom : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).keyBits≤K*h
  oldFieldRoom : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).fieldBits*(s h i).oldLanes≤K*h
  socketRoom : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).socketBits≤K*h

theorem extent_rate (r : ScalarRoom s) : Bounded (fun h i=>(s h i).endAddress 0) :=by
  let c (a : ℕ):=Bounded.const (ι:=ι) a
  have old : Bounded (fun h i=>(s h i).sourceRows) :=r.oldHosts.mul
    ((r.oldGroups.add r.oldLanes).of_le (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)))
  have next : Bounded (fun h i=>(s h i).nextRows) :=r.hosts.mul
    ((r.groups.add r.lanes).of_le (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)))
  have cols : Bounded (fun h i=>(s h i).fields) :=(c 15).mul (((r.blocks.mul r.oldSlots).mul (c 11)))
  obtain ⟨K₀,oldBound⟩:=r.joinRoom
  obtain ⟨K₁,newBound⟩:=r.socketRoom
  have keys : Bounded (fun h i=>2^(s h i).keyBits) :=Bounded.pow_of_linear oldBound
  have proj : Bounded (fun h i=>2^(s h i).socketBits) :=Bounded.pow_of_linear newBound
  have last:=Overlap.address_rate (cols.mul r.oldHosts) r.oldGroups r.oldLanes (r.lanes.mul r.blocks) r.oldFieldRoom
  have chart : Bounded (fun h i=>(s h i).chartWords) :=
    old.add (old.add (r.reach.mul ((r.oldLanes.add (c 1)).mul (r.reach.add (c 1)))))
  have guard : Bounded (fun h i=>(s h i).chartGuard) :=
    ((chart.add old.padded).add (((r.oldLanes.add (c 1)).mul (r.reach.add (c 1))).padded)).add ((r.oldHosts.mul r.reach).padded)
  have start : Bounded (fun h i=>(s h i).overlapStart 0) :=
    ((((((c 0).add guard).add ((c 2).mul keys)).add ((old.add (c 1)).padded)).add (cols.mul (keys.add old.padded))).add
      (((cols.mul old).add (c 1)).padded))
  have room:=((start.add last).add (((c 4).mul r.blocks).mul proj)).add
    ((r.reach.add (c 2)).mul ((next.add (c 1)).padded))
  apply room.of_le
  intro h i
  unfold endAddress mapsStart projectionStart
  rw [Overlap.address_affine ((s h i).overlapStart 0)]


end MaterialExtent
end
end Hierarchy.DescentDatedAddressBook

end OAI
