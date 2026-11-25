import OAI.Hierarchy.TraceReceiverSeedBudget
import OAI.ThreeFlat.Diagonal.CursorSeedSites

namespace OAI
/-! # Initial physical work and clipped input pairs in the S43 charge table -/

namespace Hierarchy.TraceReceiverSeedWords
open ThreeFlat Diagonal Diagonal.LaneCursor Diagonal.HistoryContraction
open Diagonal.TraceSourceOwner Diagonal.CompressorPacking Diagonal.NavigationPass
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.NavigationNodeRows
open scoped Classical BigOperators
noncomputable section

private theorem clip_pair_count (S cap lane : ℕ) :
    (min (2*cap) (S-2*(lane*cap))+1)/2 = min ((S+1)/2-lane*cap) cap := by
  omega

variable {F : Type} [Field F] [Fintype F] {k low W pc regs words S base fuel : ℕ}
  (M : Machine W pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
  (hF : Fintype.card F≤2^W) (st : Word W) (B : PhysicalStage.Block F) (hk : 2≤k+1)
private abbrev pubGrid :=
  TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words ((k+1)+low)

private abbrev pubShape :=
  TraceSourceOwner.shape W pc regs words S fuel ((k+1)+low) (pubGrid M t hF st).internal

private abbrev pubState :=
  B.cursorState hk low (1+(((k+1)+low)+((k+1)+low))) (pubGrid M t hF st).cells

/-- The clipped last odd external bit contributes one physical pair charge. -/
theorem seed_pair_column (v : PairedCursor.Site (k+1)) :
    pairs M t hF st v =
      let row := B.cursorOrdinal hk low (1+(((k+1)+low)+((k+1)+low))) (pubGrid M t hF st).cells v.1 v.2
      if row<2^(k+1) then min ((S+1)/2-row*2^low) (2^low) else 0 := by
  let lane:=(finFunctionFinEquiv v.2).val
  by_cases zero : v.1=0
  · have ord : B.cursorOrdinal hk low (1+(((k+1)+low)+((k+1)+low))) (pubGrid M t hF st).cells v.1 v.2 = lane := by
      simp [B.cursorOrdinal_eq,zero,lane]
    have small : lane<2^(k+1) := (finFunctionFinEquiv v.2).isLt
    simp only [pairs,width,ite_eq_left zero,bitIndex_pinCount,ord,ite_eq_left small,pinCount,pinSpan,
      Nat.one_mul,Nat.mul_one]
    rw [show lane*(2*2^low)=2*(lane*2^low) by ring]
    exact clip_pair_count S (2^low) lane
  · have high : ¬B.cursorOrdinal hk low (1+(((k+1)+low)+((k+1)+low))) (pubGrid M t hF st).cells v.1 v.2 < 2^(k+1) := by
      intro lower
      have d:=Nat.div_eq_of_lt lower
      rw [B.cursorOrdinal_div] at d
      exact zero (Fin.ext d)
    simp [pairs,width,zero,high]

/-- The actual canonical all-bit native seed meets both initial column equations of S43. -/
theorem seedRows (A : Archive) (ax : k+1=A.axes) (lanes : A.remainingLanes=2^(k+1))
    (degree : 2^(B.exponent 0)=A.initialDegree) (wire : A.relayWidth=2^low*((1+(((k+1)+low)+((k+1)+low)))*(pubGrid M t hF st).cells*3))
    (b : Banks) (bankLanes : b.lanes=2^(k+1)) (perLane : b.perLanePairs=2^low)
    (totalPairs : b.totalPairs=(S+1)/2)
    (trace : b.traceWork=TraceBitHeader.seedTraceWork low (pubShape M t hF st).stride (pubGrid M t hF st).cells B.cursorCopies ((k+1)+low)) :
    PhysicalStage.State.SeedRows (A.cursorSeedSites B hk low (1+(((k+1)+low)+((k+1)+low))) (pubGrid M t hF st).cells ax lanes)
      A.seedData b (start M t hF st B hk) (pairs M t hF st) := by
  intro prior v col
  let r:=(A.cursorSeedSites B hk low (1+(((k+1)+low)+((k+1)+low))) (pubGrid M t hF st).cells ax lanes).ord v
  change A.seedData.cost b prior r col=_
  have row : r.val=B.cursorOrdinal hk low (1+(((k+1)+low)+((k+1)+low))) (pubGrid M t hF st).cells v.1 v.2 :=
    A.cursorSeedSites_ord B hk low (1+(((k+1)+low)+((k+1)+low))) (pubGrid M t hF st).cells ax lanes v
  have sumWidth : (A.seedData.halfWidth r).sum=(pubState M t hF st B hk).incidentWidth v := by
    change (List.replicate (2*A.initialDegree) A.relayWidth).sum=_
    simp only [List.sum_replicate,nsmul_eq_mul,PhysicalStage.State.incidentWidth,B.cursorState_width,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,degree,wire]
    let extent := 2^low*((1+(((k+1)+low)+((k+1)+low)))*(pubGrid M t hF st).cells*3)
    change (2*A.initialDegree)*extent=A.initialDegree*(extent+extent)
    ring
  have empty : (∑ i, prior (A.seedData.child r i) col)=0 := by
    change (∑ i : Fin 0, prior (A.seedData.child r i) col)=0
    simp
  have iffLeaf : B.cursorOrdinal hk low (1+(((k+1)+low)+((k+1)+low))) (pubGrid M t hF st).cells v.1 v.2 < 2^(k+1) ↔ v.1=0 := by
    let offsets := 1+(((k+1)+low)+((k+1)+low))
    let cells := (pubGrid M t hF st).cells
    let axis : Fin (k+1) := v.1
    constructor
    · intro hit
      exact Fin.ext ((B.cursorOrdinal_div hk low offsets cells axis v.2).symm.trans (Nat.div_eq_of_lt hit))
    · intro first
      have zero : axis.val=0 := congrArg Fin.val first
      calc
        _ = axis.val*2^(k+1)+(finFunctionFinEquiv v.2).val := B.cursorOrdinal_eq hk low offsets cells axis v.2
        _ = (finFunctionFinEquiv v.2).val := by rw [zero,Nat.zero_mul,Nat.zero_add]
        _ < _ := (finFunctionFinEquiv v.2).isLt
  have leaf : (A.seedLayer.kind=0 ∧ r.val<b.lanes) ↔ v.1=0 := by
    simp only [show A.seedLayer.kind=0 from rfl, true_and,bankLanes,row]
    exact iffLeaf
  have below : r.val<b.lanes ↔ v.1=0 := by
    rw [bankLanes,row]
    exact iffLeaf
  have clip := seed_pair_column M t hF st B hk v
  have pair : (if A.seedLayer.kind=0 ∧ r.val<b.lanes then min (b.totalPairs-r.val*b.perLanePairs) b.perLanePairs else 0) =
      pairs M t hF st v := by
    simp only [show A.seedLayer.kind=0 from rfl, true_and,bankLanes,totalPairs,perLane,row]
    exact clip.symm
  have inactive (off : v.1≠0) : pairs M t hF st v=0 :=
    clip.trans (ite_eq_right (fun hit=>off (iffLeaf.mp hit)))
  simp only [LayerData.cost,pair,empty,Nat.add_zero]
  simp only [show A.seedLayer.kind=0 from rfl,true_and,ite_true,sumWidth,start,trace]
  by_cases active : v.1=0
  · have hit := below.mpr active
    simp [hit,active,Nat.add_assoc]
  · have miss := mt below.mp active
    simp [miss,active,inactive active]


end
end Hierarchy.TraceReceiverSeedWords

end OAI
