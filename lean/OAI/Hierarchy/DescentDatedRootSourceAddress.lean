import OAI.Hierarchy.DescentOperandSourceAddressPieces
import OAI.Hierarchy.DescentDatedOperandRootSize
import OAI.Hierarchy.DescentDatedOperandHeadBill
import OAI.Hierarchy.DescentDatedPriorOperandRate
import OAI.Hierarchy.DescentDatedMaterialExtent

namespace OAI
/-! All physical pages from the newborn mouth through the final ticket resolver input. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentHaloWalkRAM DescentRawCablePanel
open DescentSIMDLookup DescentSharedCableNames Filter
noncomputable section
set_option quotPrecheck false
variable {ι : ℕ→Type*} {F : Type} [Field F] {Pins : ∀h,ι h→Type} (v : ∀h (i : ι h),PhysicalOrdinary F (Pins h i))
local notation "d_" => fun h i=>(v h i).ticket.depotShape (v h i).short
local notation "m_" => fun h i=>(v h i).material
local notation "r_" => fun h i=>(v h i).resolver
local notation "g_" => fun h i=>(v h i).ticketReadGeometry

/-- Translating an old sorted walk uses two input numerals and one result.
The final ordinary path selector reserves a third input at this same candidate count. -/
theorem sorted_path_stage_le (g : Geometry) : g.stageWords 2 1 g.paths≤g.pipelineWords :=by
  have exponent : g.digitBits*2+g.digitBits≤g.digitBits*3+g.digitBits:=by omega
  have table: 2^((g.digitBits*2+g.digitBits)*g.lanes)≤2^((g.digitBits*3+g.digitBits)*g.lanes):=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right g.lanes exponent)
  have head : g.stageWords 2 1 g.paths≤g.stageWords 3 1 g.paths:=by
    unfold Geometry.stageWords
    omega
  apply head.trans
  change _≤_+g.stageWords 3 1 g.paths+_
  omega

theorem root_source_rate (material : MaterialExtent.ScalarRoom m_)
    (resolver : DescentDatedPriorOperand.Layout.ScalarRoom r_)
    (degree : Bounded (fun h i=>((d_) h i).degree))
    (payload : Linear (fun h i=>(v h i).payload))
    (selected : ∀h i,(v h i).signed=(v h i).signedLayout.format (v h i).payload)
    (birth : Linear (fun h i=>((v h i).bornBook.bits*((r_) h i).nodes)*((r_) h i).lanes))
    (purchased : Linear (fun h i=>purchase ((g_) h i)*((g_) h i).lanes))
    (digits : Linear (fun h i=>(v h i).operandShortBits)) :
    Bounded (fun h i=>(v h i).rootSourceSize) :=by
  let cst:=fun n=>Bounded.const (ι:=ι) n
  have cap : Bounded (fun h i=>((d_) h i).cap):=material.oldSlots
  have block : Bounded (fun h i=>((d_) h i).blocks):=material.blocks
  have path : Bounded (fun h i=>breadth ((d_) h i).degree):=(degree.add (cst 1)).pow 4
  have sourceKey : Linear (fun h i=>DepotRAM.totalBits ((d_) h i)*((m_) h i).oldLanes):=
    Linear.smaller material.joinRoom fun h i=>Nat.mul_le_mul_right _ (Nat.le_add_right ..)
  have cols : Bounded (fun h i=>DescentDatedOperandPages.count ((d_) h i)):=
    (block.mul (degree.mul (cap.mul (cst 4)))).add (block.mul (cap.mul (cst (3*5))))
  have old:=DescentDatedOperandPages.extent_rate d_ (fun h i=>(v h i).operandDepotLayout)
    material.oldHosts material.oldGroups material.oldLanes (material.lanes.mul material.blocks)
    cols sourceKey material.oldFieldRoom
  have oldHead:=path.mul (block.mul (degree.mul cap))
  have anchored:=path.mul (block.mul (cap.mul (cst 3)))
  have raw:=path.mul (block.mul (cap.mul (cst 11)))
  have branches:=path.mul (degree.add (cst 1))
  have wideFields:= (block.mul ((cst 4).mul oldHead)).add
    ((block.mul ((cst 5).mul anchored)).add (block.mul ((cst 8).mul raw)))
  have wk:=payload.smaller fun h i=>((v h i).head_signed_width (selected h i)).1.trans (Nat.div_le_self ..)
  have nk:=payload.smaller fun h i=>((v h i).head_signed_width (selected h i)).2.trans (Nat.div_le_self ..)
  have first:=DescentOrdinaryHeadRetile.Shape.address_rate (fun h i=>(v h i).wideHeads) wideFields
    material.hosts material.groups material.lanes resolver.lanes wk
  have second:=DescentOrdinaryHeadRetile.Shape.address_rate (fun h i=>(v h i).narrowHeads) (branches.add path)
    material.hosts material.groups material.lanes resolver.lanes nk
  have jobs:=resolver.blocks.mul (resolver.nodes.mul resolver.arities)
  have choices (q : Fin 5) : Bounded (fun h i=>candidateCount ((g_) h i) q):=by
    fin_cases q
    · exact oldHead
    · exact branches
    · exact anchored
    · exact raw
    · exact path
  have final_:=pipeline_rate g_ resolver.hosts resolver.groups resolver.lanes jobs choices purchased
  have width : Linear (fun h i=>(v h i).operandShortBits*((r_) h i).lanes):=purchased.smaller fun h i=>
    Nat.mul_le_mul_right _ ((Nat.le_mul_of_pos_left _ (by decide : 0<18)).trans (le_max_left ..))
  have previous:=Linear.table (show Linear (fun h i=>((((r_) h i).size+2)*((r_) h i).nodes)*((r_) h i).lanes) by
    obtain ⟨K,fit⟩:=resolver.width
    exact ⟨K,fit.mono fun h hi i=>(hi i).1⟩)
  have col:=old.add (branches.mul material.oldHosts.padded)
  have stride_ :=(material.oldHosts.mul (material.groups.chunks material.lanes)).padded
  have pathWords:=((material.lanes.add (cst 1)).mul (path.add (cst 1)).padded).padded
  have broadcast:=(col.add ((cst 2).mul stride_)).add pathWords
  have rank:=(broadcast.add (path.mul material.oldHosts.padded))
  have publicRows:=(resolver.hosts.mul (resolver.groups.chunks resolver.lanes)).padded
  have publicWords:=((resolver.lanes.add (cst 1)).mul digits.table).padded
  have publicTable:=((cst 0).add ((cst 2).mul publicRows)).add publicWords
  have translation:=publicTable.add (final_.of_le (fun h i=>sorted_path_stage_le ((g_) h i)))
  exact ((((((rank.add (resolver.nodes.mul previous)).add (resolver.nodes.mul birth.table)).add
    (first.add second)).add ((cst 4).mul width.table)).add translation).add final_)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
