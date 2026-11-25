import OAI.ThreeFlat.Diagonal.TraceJournalRows
import OAI.Hierarchy.TraceDescriptorScan
import OAI.Hierarchy.TraceNativeAdmittedWork
import OAI.ThreeFlat.Diagonal.PhysicalNodeDirectoryCap
import OAI.ThreeFlat.Diagonal.InitialMetadataScan

namespace OAI
/-! # Protected seed and finite bounds for both forms of trace recovery -/
namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows Computability.VPVNP.BurstRAM TraceDistribution TraceRecovery
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (B : Block F)

theorem registered_charges (Pins : Type) (n rem : ℕ) {lanes : ℕ}
    (X : State (2^B.exponent 0) lanes) (e : lanes=(B.repeat n).charge+rem) :
    (Program.certRecast e X _ ((B.repeat n).certifiedCharges B.costFactors.sum (B.factor_bound n) rem (e ▸ X))).1 =
      (Physical.registerOnLanes B Pins n rem X e).2 := by
  subst lanes
  rfl

/-- The same protected seed and allocator bounds feed both the semantic and the
word-assembly journal reconstruction. -/
theorem recovery_seed {W limit : ℕ} (n rem v : ℕ) (a : Archive)
    (Y : State (2^B.exponent 0) ((B.repeat n).charge+rem)) (base : Fintype.card Y.Base=v)
    {cur ctr : Word W} (raw : List Bool) {input final : Memory W}
    (journal : a.TraceJournal limit cur ctr (B.repeat n) rem Y a.cursor raw input final)
    (reads : a.seedData.Reads (fun z=>(input z).val))
    (foot : a.seedData.Footprint (fun z=>a.initialRecords≤z ∧ z<a.metadataEnd) (fun z=>(input z).val))
    (halves : 2*a.initialDegree≤directoryCap B) (controls : cur.val<ctr.val) :
    let ops:=(B.repeat n).directory rem v
    let stop:=finish a.K ops a.cursor
    stop.header≤a.initialRecords → a.metadataEnd≤a.cursor.heap → a.cursor.heap≤cur.val →
    stop.header≤a.cursor.heap →
    a.cursor.node+a.seedLayer.count+(ops.map Stage.nodes).sum+(ops.map successors).sum≤2^W →
    RowContents a.seedData (·<stop.heap) (fun z=>(final z).val) (directoryCap B) (directoryCap B) ∧
    JournalSpace a.K W (directoryCap B) (directoryCap B) ((B.repeat n).directory rem (Fintype.card Y.Base))
      a.cursor a.seedLayer (·<stop.heap) := by
  intro ss stop seedStart seedEnd arenaCur headers nodes
  have before : a.cursor.heap ≤ stop.heap := by dsimp only [stop];rw [heap_finish];omega
  have safe (z : ℕ) (lo : a.initialRecords≤z) (hi : z<a.metadataEnd) :
      traceOutsideWrites a.K a.cursor ((B.repeat n).directory rem (Fintype.card Y.Base)) z := by
    rw [base]
    exact ⟨.inr (seedStart.trans lo),.inl (hi.trans_le seedEnd)⟩
  refine ⟨TraceRecovery.seed_contents (H:=directoryCap B) (M:=directoryCap B) (dp:=stop.heap)
    (B.repeat n) rem Y raw journal reads foot halves (seedEnd.trans before) (seedEnd.trans arenaCur) controls safe,?_⟩
  rw [base]
  have prior:=JournalSpace.of_rooms (W:=W) (K:=a.K) (layer:=a.seedLayer)
    (c:=a.cursor) (ops:=ss) (dp:=stop.heap) rfl nodes headers le_rfl
  exact ⟨prior.nodes,prior.header,prior.arena,fun op hit=>(directory_member_cap B n rem v op hit).2⟩

theorem recovery_bound {W n K Z : ℕ} (alphabet : K=B.alphabetCap) (budget : B.repeatFactor*Z<2^W)
    (b : ℕ×ℕ) (hit : b∈(B.repeat n).recordBounds) : b.1≤K ∧ b.2*Z<2^W := by
  rw [alphabet]
  exact ⟨Block.component_le Prod.fst (B.bounds_repeat n hit),
    (Nat.mul_le_mul_right Z (Block.component_le Prod.snd (B.bounds_repeat n hit))).trans_lt budget⟩

end
end Hierarchy.TraceAdmission

end OAI
