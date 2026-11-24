import OAI.Computability.VPVNP.CompressorGroupCost
import OAI.Computability.VPVNP.CompressorShrinkSelectedGroup
import OAI.Computability.VPVNP.CompressorShrinkResidentCosts
import OAI.Computability.VPVNP.CompressorShrinkLevelSpace

/-! # Calls and probes of installed selected shrinking geometry -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BlockPlanner BurstRAM Schedule

/-- The catalog bounds frame probes per source call and scheduler probes
per packet. Both constants are fixed with the script. -/
def groupRate (A : Script) (dataRate rowRate : ℕ) :=
  dataRate*(arity A.catalog+3)+rowRate*(Online.Run.maxReads A.plan+4*arity A.catalog+26)

theorem groupCost_le {w : ℕ} (A : Script) (ps : List (SourceOnline.Packet A w)) (units dataRate rowRate : ℕ)
    (data : RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) ≤ units*dataRate)
    (rows : ps.length ≤ units*rowRate) : groupCost A ps ≤ units*groupRate A dataRate rowRate := by
  rw [groupRate,Nat.mul_add,← Nat.mul_assoc,← Nat.mul_assoc]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ data) (Nat.mul_le_mul_right _ rows)

end CompressorRecords.ScheduledTrace

namespace CompressorRecords.SelectedTailPackets

open BurstRAM Compression BlockPlanner DescriptorSpace Schedule ScheduledTrace
open scoped Fin.CommRing Classical
open private positions_eq packed_le from OAI.Computability.VPVNP.CompressorShrinkLevelSpace

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a g w : ℕ} (X : State a (packingLaneBits a g))
variable (T : IncidenceDirectory w) (start : ℕ) (stride selectors : Word w)
variable {fuel : ℕ} {s : SelectedScore.Selection B X} {m : Memory w} {p : ShrinkBranch.Prefix X T start fuel m}
variable (v : ShrinkBranch.Selected B X T start stride selectors fuel m p s)

/-- Source cost per incoming position. It uses the stronger dense-motif
bound of one motif per old arc. -/
def geometryRate (a : ℕ) := 51*2^a+23

theorem geometry_charge :
    RAMBuckets.cost Report.probes v.geometry.reports ≤ X.positions*geometryRate a ∧
      v.geometry.reports.length = selectedCalls X := by
  let P := X.positions
  let M := SelectedArena.motifs X
  let V := ShrinkPreimages.newCount X
  let old := SelectedArena.positions X
  let arcs := DemandRAM.oldCount X
  have hp : old=P := positions_eq X
  have ho : ShrinkPreimages.oldCount X=P := positions_eq X
  have ha : arcs=P*2^a := congrArg (·*2^a) (positions_eq X)
  have hm : M ≤ P*2^a := (ShrinkResidentLayout.motif_le_slots X).trans_eq (congrArg (·*2^a) ho)
  have hv : V ≤ P := packed_le X
  have pos : 1 ≤ P := X.positions_pos
  have ch := ChosenGeometry.Run.charge B X _ stride selectors _ T s _ _ v.geometry v.postTerm
  change RAMBuckets.cost Report.probes v.geometry.reports = (40*M+7)+9*old+11*arcs+(2*V+5*ShrinkPreimages.oldCount X) at ch
  constructor
  · rw [ch,hp,ha,ho]
    change _ ≤ P*(51*2^a+23)
    rw [Nat.mul_add,Nat.mul_left_comm P 51]
    linarith only [hm,hv,pos]
  · let calls {Q : Type} {prog : BurstRAM.Program w Q} {f : ℕ} {st : Option (Word w)} {mem : Memory w} {n : ℕ} {rs : List (Report w)}
        (h : runSegment prog f st mem (List.replicate n [])=some rs) : rs.length=n := by
          simpa only [branchPaths,List.length_map,List.length_replicate] using congrArg List.length ((runSegment_iff ..).mp h).2.2
    have len := v.postTerm.scores
    have lp := calls v.postTerm.placed.positions
    have lr := calls v.postTerm.placed.roles
    have lc := v.postTerm.geometry.raw.clearCount
    have la := v.postTerm.geometry.raw.collectCount
    simp only [ChosenGeometry.Construction.reports,SelectedStage.Passes.all,List.length_append,len,lp,lr,lc,la,selectedCalls,Nat.add_assoc]

/-- Changing the two score cursors preserves the number of calls and the
full event log, hence the exact calls-plus-probes cost. -/
theorem geometry_cost_eq {A : Script} {mem : Memory w} {ps : List (SourceOnline.Packet A w)}
    (chron : SourceWalk.Chronological SourceOnline.Visit.Runs mem ps)
    (events : eventLog (ps.flatMap SourceWalk.Packet.reports)=eventLog v.geometry.reports)
    (tapes : ps.flatMap (fun q => q.stage.choices)=List.replicate (selectedCalls X) []) :
    RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) = RAMBuckets.cost Report.probes v.geometry.reports := by
  have count := congrArg List.length ((PublishedHeads.chronological_tapes mem ps chron).symm.trans tapes)
  simp only [branchPaths,List.length_map,List.length_replicate] at count
  rw [SourceOnline.packet_cost,SourceOnline.packet_cost,events,count,(geometry_charge B X T start stride selectors v).2]

/-- Pass the exact report boundary and choice count of the fourteen installed
rows to the scheduler's weighted cost. -/
theorem geometry_groupCost {A : Script} {L : Layout} {base : Word w} {cap ordinal total : ℕ}
    {mem : Memory w} {ps : List (SourceOnline.Packet A w)}
    (group : SourceOnline.Group A L base cap ordinal total mem ps) (rows : ps.length=14)
    (events : eventLog (ps.flatMap SourceWalk.Packet.reports)=eventLog v.geometry.reports)
    (tapes : ps.flatMap (fun q => q.stage.choices)=List.replicate (selectedCalls X) []) :
    groupCost A ps ≤ X.positions*groupRate A (geometryRate a) 14 := by
  have data := geometry_cost_eq B X T start stride selectors v group.chronological events tapes
  apply groupCost_le A ps _ _ _ (data.le.trans (geometry_charge B X T start stride selectors v).1)
  rw [rows]
  exact Nat.le_mul_of_pos_left _ X.positions_pos

end CompressorRecords.SelectedTailPackets

end VPVNP
end Computability
end OAI
