import OAI.Hierarchy.DescentReachedOrdinaryBook

namespace OAI
/-! # The group, block and dense native rack number of every reached scalar row -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)

/-- The actual native output row uses exactly the group, block and full host
address carried by the winner's two merged venue coordinates. -/
theorem reached_location (age : i<S.length) (radix : S.radix=2^k) (v : n.result.graph.Site)
    (x : ((ticket.advance arch).bit.recipe v).Node) :
    let label:=splitKey (currentLabel ticket arch v x).val
    let key:=label.2
    let slots:=2^DescentHostDegree.packExponent 20 cap.placement.degree+2
    ((target.placement.pos v).1,target.placement.block v)=S.groupDigits age radix label.1 ∧
    (target.vertex (target.placement.pos v).2).val=((cap.vertex key.1).val*(2^(k+1)-1)+
      nodeNumber key.2.1.1 key.2.1.2)*slots+key.2.2 := by
  obtain rfl := ticket.sourceRate
  obtain rfl := eq_of_heq ticket.placement
  obtain ⟨_,_,chart,place,ordinal⟩:=ticket.venueRows
  let origin:=roots ticket arch ⟨v,x⟩
  let actor:=rawNodeSite (he:=he) (T:=cap.placement.stage) (c:=c) arch origin
  let rows := BitDescription.scannedRows he cap.placement.stage
  have addr:=place (rows.state c) (activeChart ticket) actor
  have dest : n.destination (rawInput he cap.placement.stage c (rows.state c) actor)=v :=
    roots_owner ticket arch ⟨v,x⟩
  dsimp only at addr
  rw [dest] at addr
  have h : chart (target.placement.pos v).2=(splitKey (currentLabel ticket arch v x).val).2 := addr.2
  refine ⟨addr.1,?_⟩
  rw [ordinal,h]

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
