import OAI.Hierarchy.DescentRetainedTargetPlacementChart
import OAI.Hierarchy.DescentDatedRetainedPlacementRate

namespace OAI
/-! # Address bound for the common shape-indexed retained placement lookup -/
namespace Hierarchy.DescentRetainedTargetPlacement.Chart
open DescentDatedAddressBook DescentResetRetainedPlacement DescentSIMDLookup
noncomputable section
variable {ι : ℕ→Type*} (p : ∀h,ι h→DescentResetRetainedPlacement.Chart) (b : ∀h,ι h→Batch)

theorem extent_rate (r : DescentResetRetainedPlacement.Chart.ScalarRoom p b) :
    Bounded fun h i=>endAddress (p h i) (b h i) 0 :=by
  let wide:=fun h i=>expanded (p h i) (b h i)
  have larger : DescentResetRetainedPlacement.Chart.ScalarRoom p wide :=
    ⟨r.oldHosts,r.newHosts,r.shapes,r.groups,r.blocks,r.lanes,r.fields.mul r.shapes,r.oldLanes,r.source,r.target⟩
  have placed:=DescentResetRetainedPlacement.Chart.extent_rate p wide larger
  have proj : Bounded (fun h i=>(p h i).projected (wide h i) 0) :=by
    apply placed.of_le
    intro h i
    let v:=p h i
    let batch:=wide h i
    calc
      v.projected batch 0 ≤ DescentResetRetainedPlacement.Chart.directory v batch 0 :=
        Nat.le_add_right _ (DescentResetRetainedPlacement.Chart.route v batch 0).size
      _ ≤ DescentResetRetainedPlacement.Chart.samples v batch 0 :=
        Nat.le_add_right _ (2*2^Nat.clog 2 v.rows+2^Nat.clog 2 v.sparse)
      _ ≤ DescentResetRetainedPlacement.Chart.samples v batch 0+(batch.fields*v.blocks)*v.rows := Nat.le_add_right _ _
      _ ≤ DescentResetRetainedPlacement.Chart.endAddress v batch 0 :=
        Nat.le_add_right _ (DescentResetRetainedPlacement.Chart.rounded v.rows)
  let c j:=Bounded.const (ι:=ι) j
  have parts : Bounded (fun h i=>(p h i).parts):=
    (r.groups.add r.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have guard_:=((((r.shapes.add (c 1)).mul r.blocks).mul (r.oldHosts.mul parts)).add (c 1)).padded
  have sparse:=r.oldHosts.mul r.shapes
  have rows:=r.newHosts.mul parts
  have directory_:=(proj.add ((c 2).mul guard_)).add ((sparse.mul parts).add (c 1)).padded
  have samples_:=directory_.add (((c 2).mul rows.padded).add sparse.padded)
  exact (samples_.add ((r.fields.mul r.blocks).mul rows)).add (rows.add (c 1)).padded

end
end Hierarchy.DescentRetainedTargetPlacement.Chart

end OAI
