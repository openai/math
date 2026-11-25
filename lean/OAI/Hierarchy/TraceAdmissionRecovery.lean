import OAI.Hierarchy.TraceAdmissionRecoverySeed
import OAI.ThreeFlat.Diagonal.TraceJournalRecovery
import OAI.Hierarchy.TraceDescriptorScan
import OAI.Hierarchy.TraceNativeAdmittedWork
import OAI.ThreeFlat.Diagonal.PhysicalNodeDirectoryCap

namespace OAI
/-! # Recovering the same numbered terminal factors as the native weighted trace -/
namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows Computability.VPVNP.BurstRAM TraceDistribution TraceRecovery
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- Reindex the physically decoded journal onto the very same public run used
by the tensor identity and the canonical node-price calculation. -/
theorem repeated_recovery {W limit k n low off slots : ℕ} (hk : 2≤k+1)
    (fits : B.blockCharge*n≤k+1) (a : Archive) (ax : k+1=a.axes)
    (lanes : a.remainingLanes=2^(k+1)) (alphabet : a.K=B.alphabetCap)
    (enough : B.repeatFactor*((B.cursorState hk low off slots).maxWidth+1)*B.widthBase^n<2^W)
    (Pins : Type) (cur ctr : Word W) (raw : List Bool) (input final : Memory W) :
    let P:=B.repeat n
    let rem:=k+1-P.charge
    let split : k+1=P.charge+rem:=by dsimp only [P,rem];rw [B.charge_repeat];omega
    let X:=B.cursorState hk low off slots
    let X':State (2^B.exponent 0) (P.charge+rem):=split ▸ X
    let ss:=P.directory rem (k+1)
    let stop:=finish a.K ss a.cursor
    let O:=a.cursorSeedSites B hk low off slots ax lanes
    let cap:=directoryCap B
    let run:=Physical.run B hk low off slots n fits
    let table:=physicalTable B hk low off slots n W fits enough
    let C:=(Physical.registerOnLanes B Pins n rem X split).2
    a.TraceJournal limit cur ctr P rem X' a.cursor raw input final →
    TraceRetainedRoom.Room limit W → 8≤W → cur.val<ctr.val →
    a.seedData.Reads (fun i=>(input i).val) →
    a.seedData.Footprint (fun z=>a.initialRecords≤z ∧ z<a.metadataEnd) (fun i=>(input i).val) →
    2*a.initialDegree≤cap → stop.header≤a.initialRecords → a.metadataEnd≤a.cursor.heap →
    a.cursor.heap≤cur.val → stop.header≤a.cursor.heap →
    a.cursor.node+a.seedLayer.count+(ss.map Stage.nodes).sum+(ss.map successors).sum≤2^W →
    Recovered run table.records C O a.seedData raw
      (stagePost a.K ss a.cursor a.seedLayer (·<stop.heap) (fun i=>(final i).val) cap cap (fun _=>False)) := by
  intro P rem split X X' ss stop O cap run table C journal room wide counters reads foot halves
    seedStart seedEnd arenaCur headers nodes
  have base : Fintype.card X'.Base=k+1 := (Program.baseCast split X).trans (Fintype.card_fin _)
  obtain ⟨seeded,space⟩:=recovery_seed B n rem (k+1) a X' base raw journal reads foot halves counters
    seedStart seedEnd arenaCur headers nodes
  let Z:=(X'.maxWidth+1)*B.widthBase^n
  have budget : B.repeatFactor*Z<2^W := by
    dsimp only [Z]
    rw [State.maxWidth_cast_lanes,←Nat.mul_assoc]
    exact enough
  have bound:=recovery_bound (n:=n) B alphabet budget
  let q:=B.recordTable B.alphabetCap W n rem X' le_rfl budget
  let charges:=P.certifiedCharges B.costFactors.sum (B.factor_bound n) rem X'
  let protect := stagePost a.K ss a.cursor a.seedLayer (·<stop.heap) (fun i=>(final i).val) cap cap (fun _=>False)
  let old:=castSites split X O
  have recovered:=TraceRecovery.reconstruct P Z B.costFactors.sum bound (B.factor_bound n) rem X'
    (B.repeat_widthCeiling n rem X') a.cursor raw journal room wide counters old
    (numbered_castSites split X O (a.cursorSeedSites_numbered B hk low off slots ax lanes))
    rfl a.seedData (·<stop.heap) cap cap seeded space
  have fixed {K : ℕ} (same : K=B.alphabetCap) (limits : ∀b∈P.recordBounds,b.1≤K ∧ b.2*Z<2^W) :
      (P.table K W Z limits rem X' (B.repeat_widthCeiling n rem X')).records=q.records := by
    subst K
    rfl
  rw [fixed alphabet bound] at recovered
  have samePost := congrArg (fun axes =>
    Recovered (P.run rem X') q.records charges.1 old a.seedData raw
      (stagePost a.K (P.directory rem axes) a.cursor old.layer (·<stop.heap)
        (fun i=>(final i).val) cap cap (fun _=>False))) base
  have canonical:=recovered_recast split X (P.run rem X') q charges O a.seedData raw protect
    (samePost.mp recovered)
  rw [registered_charges B Pins n rem X split] at canonical
  exact canonical

end
end Hierarchy.TraceAdmission

end OAI
