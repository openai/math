import OAI.Hierarchy.DescentResetRetainedPlacementChart
import OAI.Hierarchy.DescentDatedOverlapAperture

namespace OAI
/-! # The address cost of one honest projected, reindexed retained slab -/
namespace Hierarchy.DescentResetRetainedPlacement.Chart
open DescentDatedAddressBook DescentSIMDLookup ProtocolRAM Filter
noncomputable section
variable {ι : ℕ→Type*} (p : ∀h,ι h→Chart) (b : ∀h,ι h→Batch)

structure ScalarRoom : Prop where
  oldHosts : Bounded (fun h i=>(p h i).oldHosts)
  newHosts : Bounded (fun h i=>(p h i).newHosts)
  shapes : Bounded (fun h i=>(p h i).shapes)
  groups : Bounded (fun h i=>(p h i).groups)
  blocks : Bounded (fun h i=>(p h i).blocks)
  lanes : Bounded (fun h i=>(p h i).lanes)
  fields : Bounded (fun h i=>(b h i).fields)
  oldLanes : Bounded (fun h i=>(b h i).inputLanes)
  source : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(b h i).bits*(b h i).inputLanes≤K*h
  target : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,((b h i).bits*(p h i).blocks)*(p h i).lanes≤K*h

theorem extent_rate (r : ScalarRoom p b) :
    Bounded (fun h i=>(p h i).endAddress (b h i) 0) :=by
  let c (j : ℕ):=Bounded.const (ι:=ι) j
  have chunk {X Y : ∀h,ι h→ℕ} (x : Bounded X) (y : Bounded Y) :
      Bounded (fun h i=>chunks (X h i) (Y h i)) :=
    (x.add y).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have parts:=chunk r.groups r.lanes
  have oldG:=r.groups.mul r.blocks
  have newL:=r.lanes.mul r.blocks
  have H:=r.fields.mul r.oldHosts
  have copied:=((r.fields.mul (r.oldHosts.mul (chunk oldG r.oldLanes))).add (c 1)).padded
  have move:=Overlap.address_rate H oldG r.oldLanes newL r.source
  have step : Bounded (fun h i=>
      let v:=p h i;let a:=b h i;let g:=v.groups*v.blocks
      let copy:=rounded (a.fields*(v.oldHosts*chunks g a.inputLanes))
      Overlap.dest copy (a.fields*v.oldHosts) g a.inputLanes (v.lanes*v.blocks) a.bits) :=by
    apply (copied.add move).of_le
    intro h i
    dsimp only
    rw [←Overlap.address_affine]
    exact Nat.le_add_right ..
  have transpose:=step.add ((H.mul (chunk oldG newL)).add (c 1)).padded
  obtain ⟨K,hw⟩:=r.target
  have dict:=r.blocks.mul (Bounded.pow_of_linear (K:=K) hw)
  have entries:=r.fields.mul (r.blocks.mul ((r.oldHosts.mul (c 1)).mul parts))
  have book : Bounded (fun h i=>(p h i).projected (b h i) 0) :=by
    simpa only [projected,Chart.parts,Nat.zero_add,rounded] using (((((transpose.add (dict.add ((c 2).mul entries))).add
      (dict.add (c 1)).padded).add (entries.add (c 1)).padded).add entries).add
      ((r.oldHosts.mul parts).add (c 1)).padded)
  have sparse:=r.oldHosts.mul r.shapes
  have rows:=r.newHosts.mul parts
  have map:=book.add ((sparse.mul parts).add (c 1)).padded
  have rebased:=map.add (((c 2).mul rows.padded).add sparse.padded)
  exact (rebased.add ((r.fields.mul r.blocks).mul rows)).add (rows.add (c 1)).padded

theorem placed_rate (s : ∀h,ι h→Batch) (rb : ScalarRoom p b) (rs : ScalarRoom p s) :
    Bounded (fun h i=>(p h i).placedEndAddress (b h i) (s h i) 0) :=by
  apply ((extent_rate p b rb).add (extent_rate p s rs)).of_le
  intro h i
  rw [placedEndAddress,(p h i).affine (s h i)]

end
end Hierarchy.DescentResetRetainedPlacement.Chart

end OAI
