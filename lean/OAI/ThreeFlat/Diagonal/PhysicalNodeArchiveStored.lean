import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveChargeRun

namespace OAI
/-! # Native publication of the selected run's node directory and charge history -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows PhysicalStage
open scoped Fin.CommRing Classical
noncomputable section

variable {F : Type} [Field F] {W : ℕ}

/-- Execute the packed node decoder and the single counted publisher on the selected
history. Both the seed charge and every parent/child recurrence hold of the resulting RAM. -/
theorem publish_stored {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (a : NodeArchive) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a (records (r.archiveList h C O p seed)) budget)
    (tape : TapeBounds W a (records (r.archiveList h C O p seed)))
    (raw : let rows:=records (r.archiveList h C O p seed)
      Mount (image a rows.length) (tapeWord a rows) m)
    (src : SourceRows a (program (r.archiveList h C O p seed)) m)
    (start pay : A.Site→ℕ) (seeds : State.SeedRows O seed a.banks start pay)
    (fit : r.ArchiveFits W a.banks.unitWork h C start pay) :
    let xs:=r.archiveList h C O p seed
    let n:=(records xs).length
    (a.publish n).Spec (fun x=>x=m) (fun _ out=>
      out=state a (program xs) m n ∧ O.Charged a.banks (natural out) start pay ∧
        r.ArchiveRowsStored a.banks (natural out) h C O p) ((16*n*(5*W+6)+10)+(3+(3+(n*(7+budget)+4)))) := by
  let xs:=r.archiveList h C O p seed
  let P:=program xs
  have all:=archive_charge_fits r h C O p seed a m room start pay seeds fit
  have good:=ready_of_source a P m room tape src (fun i j=>all i j 1)
  have out:=archive_rows_stored r h C O p seed a m room src.preceding all
    (archive_parent_fits r h C O p seed a room)
  dsimp only
  intro labels registers slots machine pc reg pub exit installed data cfg input first initial
  obtain ⟨elapsed,bounded,final,output,advance_,return_,eq⟩ :=
    publish_spec a P m raw room good machine pc reg pub exit installed data cfg input first initial
  refine ⟨elapsed,bounded,final,output,advance_,return_,eq,?_,?_⟩
  · rw [eq]
    exact seeds.charged _ out.1
  · rw [eq]
    exact out.2

end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
