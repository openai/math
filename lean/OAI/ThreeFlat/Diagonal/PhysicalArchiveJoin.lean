import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily

namespace OAI
/-! # Joining a selected native record to its typed tail history and published rows -/

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open RAM.NavigationNodeRows HistoryContraction
noncomputable section
variable {F : Type} [Field F]

private def toCastHistory {X Y : Shape} (e : X=Y) (P : Plan F X) (h : P.History) :
    (e ▸ P : Plan F Y).History := by cases e;exact h

private theorem historyOfCast_toCast {X Y : Shape} (e : X=Y) (P : Plan F X) (h : P.History) :
    historyOfCast e P (toCastHistory e P h)=h := by cases e;rfl

variable {d l D L : ℕ} {A : State d l} (R : Move F A D L) (next : ∀t,Run F (R.next t))

/-- A genuine branch and parsed continuation give the plan's dependent history. -/
def joinHistory (j : Fin R.rules.count) (h : (next j).plan.History) :
    (Run.step R next).plan.History :=
  ⟨j,toCastHistory (R.target_eq j).symm (next j).plan h⟩

theorem joinHistory_fst (j : Fin R.rules.count) (h : (next j).plan.History) :
    (joinHistory R next j h).1=j := rfl

@[simp] theorem tailHistory_joinHistory (j : Fin R.rules.count) (h : (next j).plan.History) :
    tailHistory R next (joinHistory R next j h)=h :=
  historyOfCast_toCast (R.target_eq j).symm (next j).plan h

theorem read_joinHistory (E : (Run.step R next).Records) (raw : List Bool)
    (j : Fin R.rules.count) (hit : E.1.read (raw.take E.1.width)=some j)
    (h : (next j).plan.History) (suffix : List Bool)
    (tailHit : (next j).plan.read ((next j).codes (E.2 j)) (raw.drop E.1.width)=some (h,suffix)) :
    (Run.step R next).plan.read ((Run.step R next).codes E) raw=some (joinHistory R next j h,suffix) := by
  apply (read_step_eq R next E raw suffix _).2
  refine ⟨hit,?_⟩
  change (next j).plan.read ((next j).codes (E.2 j)) (raw.drop E.1.width)=
    some (tailHistory R next (joinHistory R next j h),suffix)
  rw [tailHistory_joinHistory]
  exact tailHit

/-- Append the verified rows of one physical stage to its parsed chronological tail. -/
def joinArchivePath (C : (Run.step R next).Charges) (old : A.ArchiveSites) (j : Fin R.rules.count)
    (h : (next j).plan.History) (row : R.ArchiveStep j old (C.1 j))
    (p : (next j).ArchivePath h (C.2 j) row.sites) :
    (Run.step R next).ArchivePath (joinHistory R next j h) C old :=
  ⟨row,(tailHistory_joinHistory R next j h).symm ▸ p⟩

private theorem archiveList_pathCast {d l : ℕ} {A : State d l} (r : Run F A)
    {h h' : r.plan.History} (e : h=h') (C : r.Charges) (old : A.ArchiveSites)
    (p : r.ArchivePath h C old) (data : LayerData old.layer) :
    r.archiveList h' C old (e ▸ p) data=r.archiveList h C old p data := by cases e;rfl

theorem archiveList_joinArchivePath (C : (Run.step R next).Charges) (old : A.ArchiveSites)
    (j : Fin R.rules.count) (h : (next j).plan.History) (row : R.ArchiveStep j old (C.1 j))
    (p : (next j).ArchivePath h (C.2 j) row.sites) (data : LayerData old.layer) :
    (Run.step R next).archiveList (joinHistory R next j h) C old (joinArchivePath R next C old j h row p) data =
      ⟨old.layer,⟨false,row.sites.layer.first,row.ownerPtr⟩,data,
        fun i=>(row.sites.ord (R.parent j (old.ord.symm i))).val⟩ ::
      (next j).archiveList h (C.2 j) row.sites p row.data := by
  change _ :: _ = _ :: _
  exact congrArg (_ :: ·) (archiveList_pathCast (next j) (tailHistory_joinHistory R next j h).symm
    (C.2 j) row.sites p row.data)

private theorem finalArchive_layer_pathCast {d l : ℕ} {A : State d l} (r : Run F A)
    {h h' : r.plan.History} (e : h=h') (C : r.Charges) (old : A.ArchiveSites)
    (p : r.ArchivePath h C old) :
    (r.finalArchive h' C old (e ▸ p)).1=(r.finalArchive h C old p).1 := by cases e;rfl

theorem finalArchive_layer_joinArchivePath (C : (Run.step R next).Charges) (old : A.ArchiveSites)
    (j : Fin R.rules.count) (h : (next j).plan.History) (row : R.ArchiveStep j old (C.1 j))
    (p : (next j).ArchivePath h (C.2 j) row.sites) :
    ((Run.step R next).finalArchive (joinHistory R next j h) C old (joinArchivePath R next C old j h row p)).1 =
      ((next j).finalArchive h (C.2 j) row.sites p).1 :=
  finalArchive_layer_pathCast (next j) (tailHistory_joinHistory R next j h).symm (C.2 j) row.sites p

end
end ThreeFlat.Diagonal.PhysicalStage.Run

end OAI
