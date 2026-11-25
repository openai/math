import OAI.ThreeFlat.Diagonal.PhysicalNodeStoredPath
import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge

namespace OAI
/-! # Readback of the terminal selected incidence rows -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows PhysicalStage
open scoped Fin.CommRing Classical
noncomputable section
variable {F : Type} [Field F]
private theorem terminal_row {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer) :
    ∃ q∈r.archiveList h C O p seed,q.layer=(r.finalArchive h C O p).1 := by
  induction r with
  | done A => exact ⟨_,List.mem_cons_self ..,rfl⟩
  | step R next ih =>
    obtain ⟨q,mem,eq⟩:=ih h.1 (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data
    exact ⟨q,List.mem_cons_of_mem _ mem,eq⟩

/-- The selected terminal site's S44 incident pointer in the completed native
publication. The index is the absolute terminal index used by the stage scan. -/
theorem final_incident {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    {W budget : ℕ} (a : NodeArchive) (m : Memory W)
    (room : RunBounds W a (records (r.archiveList h C O p seed)) budget) (z : (r.plan.finish h).Site) :
    let xs:=r.archiveList h C O p seed
    let terminal:=r.finalArchive h C O p
    let j:=terminal.2 ((r.finalSite h).symm z)
    state a (program xs) m (records xs).length (a.banks.nodes+8*(terminal.1.first+j.val)+6) =
      ((terminal.1.incident+2*j.val:ℕ):Word W) := by
  let xs:=r.archiveList h C O p seed
  obtain ⟨q,mem,eq⟩:=terminal_row r h C O p seed
  obtain ⟨i,viewEq⟩:=every_view xs q mem
  have row : ((records xs).get i).actual=(r.finalArchive h C O p).1 :=
    (congrArg NodeRow.layer viewEq).trans eq
  let j:=(r.finalArchive h C O p).2 ((r.finalSite h).symm z)
  let k : Fin ((records xs).get i).actual.count := ⟨j.val,by rw [row];exact j.isLt⟩
  have w:=final_node_word a (program xs) m room (archive_chronological r h C O p seed) i k (6:Fin 8)
  change state a (program xs) m (records xs).length
    (a.banks.nodes+8*(((records xs).get i).actual.first+j.val)+6)=
    ((((records xs).get i).actual.incident+j.val*2:ℕ):Word W) at w
  rw [row,Nat.mul_comm j.val 2] at w
  exact w

/-- At every actual archived stage the fixed family guard reads the emitted
S44 kind and the kernel pointer for this same physical ordinal. -/
theorem issued_guard {W : ℕ} (xs : List NodeRow) (a : NodeArchive) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a (records xs) budget) (ordered : Chronological (records xs))
    (layer : Layer) (issued : ∃q∈xs,q.layer=layer) (j : Fin layer.count) :
    let out:=state a (program xs) m (records xs).length
    let addr:=a.banks.nodes+8*(layer.first+j.val)
    out addr=(layer.kind:Word W) ∧ out (addr+5)=((layer.kernels+5*j.val:ℕ):Word W) := by
  obtain ⟨q,mem,layerEq⟩:=issued
  obtain ⟨i,view⟩:=every_view xs q mem
  have row : ((records xs).get i).actual=layer := (congrArg NodeRow.layer view).trans layerEq
  let k : Fin ((records xs).get i).actual.count:=⟨j.val,by rw [row];exact j.isLt⟩
  have zero:=final_node_word a (program xs) m room ordered i k (0:Fin 8)
  have five:=final_node_word a (program xs) m room ordered i k (5:Fin 8)
  change state a (program xs) m (records xs).length (a.banks.nodes+8*(((records xs).get i).actual.first+j.val)+0)=
    (((records xs).get i).actual.kind:Word W) at zero
  change state a (program xs) m (records xs).length (a.banks.nodes+8*(((records xs).get i).actual.first+j.val)+5)=
    ((((records xs).get i).actual.kernels+j.val*5:ℕ):Word W) at five
  rw [row,Nat.mul_comm j.val 5] at five
  simpa only [row,Nat.add_zero] using And.intro zero five


end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
