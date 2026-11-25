import OAI.Hierarchy.TraceAdmissionRecoverySeed
import OAI.ThreeFlat.Diagonal.TraceJournalWordRecovery

namespace OAI
/-! # Word assembly recovery along the original registered physical trace -/
namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows Computability.VPVNP.BurstRAM TraceDistribution TraceRecovery
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (B : Block F)

theorem registered_assembler (T : Type) (n rem : ℕ) {lanes : ℕ}
    (X : State (2^B.exponent 0) lanes) (e : lanes=(B.repeat n).charge+rem) :
    Run.inputAssembler e X _ ((B.repeat n).assembly (Pins:=T) rem (e ▸ X)) =
      (Physical.registerOnLanes B T n rem X e).1 := by
  subst lanes
  rfl

theorem repeated_word_recovery {W limit k n low off slots : ℕ} (hk : 2≤k+1)
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
    limit≤2^(W/16) → stop.header≤a.cursor.dense → 21*(2^(W/16))^4≤a.cursor.header →
    TraceWordRecovery.Words run table.records C O a.seedData raw
      (fun T => (Physical.registerOnLanes B T n rem X split).1)
      (fun T => RecordedWordStep a.K cur ctr stop.header stop.heap final T B.publicTemplate)
      (stagePost a.K ss a.cursor a.seedLayer (·<stop.heap) (fun i=>(final i).val) cap cap (fun _=>False)) := by
  intro P rem split X X' ss stop O cap run table C journal room wide counters reads foot halves
    seedStart seedEnd arenaCur headers nodes wireBase headerDense headerStart
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
  have recovered:=TraceWordRecovery.reconstruct P Z B.costFactors.sum bound (B.factor_bound n) rem X'
    (B.repeat_widthCeiling n rem X') a.cursor raw journal room wide counters old
    (numbered_castSites split X O (a.cursorSeedSites_numbered B hk low off slots ax lanes))
    rfl a.seedData (·<stop.heap) cap cap (fun _=>False) (Or.inr seeded) space B.publicTemplate (B.repeat_supported n)
    wireBase (by simpa only [base] using headerDense) headerStart le_rfl
  have fixed {K : ℕ} (same : K=B.alphabetCap) (limits : ∀b∈P.recordBounds,b.1≤K ∧ b.2*Z<2^W) :
      (P.table K W Z limits rem X' (B.repeat_widthCeiling n rem X')).records=q.records := by
    subst K
    rfl
  rw [fixed alphabet bound] at recovered
  let asm (T : Type) := P.assembly (Pins:=T) rem X'
  let vis (T : Type) : Run.WordVisit F T :=
    RecordedWordStep a.K cur ctr stop.header stop.heap final T B.publicTemplate
  let indexed (axes : ℕ) : Prop :=
    let ops := P.directory rem axes
    let endCursor := finish a.K ops a.cursor
    TraceWordRecovery.Words (P.run rem X') q.records charges.1 old a.seedData raw asm
      (fun T => RecordedWordStep a.K cur ctr endCursor.header endCursor.heap final T B.publicTemplate)
      (stagePost a.K ops a.cursor old.layer (·<stop.heap) (fun i=>(final i).val) cap cap (fun _=>False))
  have aligned := (congrArg indexed base).mp recovered
  have canonical := TraceWordRecovery.recast split X (P.run rem X') q charges O a.seedData raw asm vis protect aligned
  rw [registered_charges B Pins n rem X split] at canonical
  have assembler : (fun T : Type=>Run.inputAssembler split X (P.run rem X') (asm T)) =
      (fun T : Type=>(Physical.registerOnLanes B T n rem X split).1) :=
    funext (fun T=>registered_assembler B T n rem X split)
  rw [assembler] at canonical
  exact canonical


end
end Hierarchy.TraceAdmission

end OAI
