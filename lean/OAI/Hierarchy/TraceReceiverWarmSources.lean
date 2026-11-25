import OAI.ThreeFlat.Diagonal.PhysicalNodeArchivePath
import OAI.Hierarchy.GridReceiverNodeRegistration
import OAI.ThreeFlat.Diagonal.NativeWarmSources

namespace OAI
/-! # Recovering the selected receiver's chronological node and live stage sources -/

namespace Hierarchy.GridPhysicalAdmission.ReceiverCache
open ThreeFlat Diagonal PhysicalStage NavigationPass
open RAM Computability.VPVNP.BurstRAM RAM.NavigationNodeRows NodePublication RAM.HistoryStageSetup
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {W v directory stages budget stop : ℕ}
    {node : NodeArchive} {old : Layer} {xs : List NodeRow} {mid out saved after : Memory W}

/-- The physical publication retains each header, owner, incident, child and
kernel read of the native word assembler below the allocated terminal heap. -/
theorem wordVisits (cache : ReceiverCache v directory stages budget stop node old xs mid out saved after)
    {Pins : Type} {allow : StaticMotif F→Prop} {K head d l : ℕ} {cur ctr : Word W} {A : State d l}
    (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : A.Words Pins) (C : r.Charges)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O)
    (source : r.WordVisits (RecordedWordStep K cur ctr head stop mid Pins allow) h J L C O path) :
    r.WordVisits (RecordedWordStep K cur ctr head stop after Pins allow) h J L C O path :=
  r.wordVisits_mono _ _ (fun R i L w O c p => RecordedWordStep.transfer cache.stage_cells R i L w O c p)
    h J L C O path source

/-- On the receiver that ran the compressor, each S44 directory row has all
five authentic child, kernel, incident and external fields. Its first word is
the physical operation kind. S43 pairs are read from the same publication. -/
theorem warm_at {entry : Memory W} (cache : ReceiverCache v directory stages budget stop node old xs mid out saved after)
    (ordered : Chronological (records xs)) (chargeLo : TickWorkspace.base v 43≤node.banks.charges)
    (nodeLo : TickWorkspace.base v 43≤node.banks.nodes)
    (pub : ∀ z,TickWorkspace.base v 43≤z → z<TickWorkspace.base v 45 → entry z=saved z) :
    NativeNavigation.WarmSources v node.banks xs entry saved entry := by
  let initial := TraceAdmission.Resources.mounted (TickWorkspace.base v 41)
    (TraceAdmission.Resources.nodeWords (TickWorkspace.base v 41) node stages directory old) out
  have endRows (q : NodeRow) (mem : q∈xs) :
      node.banks.nodes+8*(q.layer.first+q.layer.count)≤TickWorkspace.base v 45 ∧
      node.banks.charges+2*(q.layer.first+q.layer.count)≤TickWorkspace.base v 45 := by
    obtain ⟨i,e⟩ := every_view xs q mem
    have eqLayer := congrArg NodeRow.layer e
    change ((records xs).get i).actual=q.layer at eqLayer
    simpa only [←eqLayer] using And.intro (cache.banks.nodeEnd i) (cache.banks.chargeEnd i)
  refine ⟨fun _ _ _=>rfl,fun _ _ _=>rfl,pub,?_,?_⟩
  · intro q mem j
    have endN := (endRows q mem).1
    have hj := j.isLt
    rw [pub _ (by omega) (by omega),cache.state_eq]
    exact (issued_guard xs node initial cache.run ordered q.layer ⟨q,mem,rfl⟩ j).1
  · intro q mem j
    obtain ⟨i,e⟩ := every_view xs q mem
    have eqLayer := congrArg NodeRow.layer e
    change ((records xs).get i).actual=q.layer at eqLayer
    have row {layer : Layer} (eq : ((records xs).get i).actual=layer) (j : Fin layer.count) :
        DirectoryRow node.banks layer j saved := by
      subst layer
      rw [cache.state_eq]
      exact published_directory node (NodePublication.program xs) initial cache.run ordered i j
    have bounds := endRows q mem
    have hj := j.isLt
    apply (row eqLayer j).retain
    · intro k _
      have hk := k.isLt
      exact pub _ (by omega) (by omega)
    · exact pub _ (by omega) (by omega)

/-- The registry itself is the first possible common entry. The same S43/S44
receipt also gives `warm_at` after the seed and S38 codebooks are mounted. -/
theorem warm (cache : ReceiverCache v directory stages budget stop node old xs mid out saved after)
    (ordered : Chronological (records xs)) (chargeLo : TickWorkspace.base v 43≤node.banks.charges)
    (nodeLo : TickWorkspace.base v 43≤node.banks.nodes)
    (pub : ∀ z,TickWorkspace.base v 43≤z → z<TickWorkspace.base v 45 → after z=saved z) :
    NativeNavigation.WarmSources v node.banks xs after saved after :=
  cache.warm_at ordered chargeLo nodeLo pub

/-- Virtual seed and codebook setup do not touch the compact archive below
its allocated heap. Rebase all retained word visits to this actual entry. -/
theorem wordVisits_at {entry : Memory W}
    (cache : ReceiverCache v directory stages budget stop node old xs mid out saved after)
    {Pins : Type} {allow : StaticMotif F→Prop} {K head d l : ℕ} {cur ctr : Word W} {A : State d l}
    (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : A.Words Pins) (C : r.Charges)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O)
    (source : r.WordVisits (RecordedWordStep K cur ctr head stop mid Pins allow) h J L C O path)
    (keep : ∀ z,z<stop → entry z=after z) :
    r.WordVisits (RecordedWordStep K cur ctr head stop entry Pins allow) h J L C O path :=
  r.wordVisits_mono _ _ (fun R i L w O c p => RecordedWordStep.transfer keep R i L w O c p)
    h J L C O path (cache.wordVisits r h J L C O path source)

end
end Hierarchy.GridPhysicalAdmission.ReceiverCache

end OAI
