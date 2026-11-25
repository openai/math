import OAI.ThreeFlat.Diagonal.TraceArchiveSource
import OAI.ThreeFlat.Diagonal.PhysicalNodeStoredPath

namespace OAI
/-! # Every selected publication read comes from the finished compressor journal -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows PhysicalStage
open NavigationDirectory TraceRecovery
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

/-- Bounds of the only writable words used by the compact publisher. -/
structure BankInterval (a : NodeArchive) (rows : List Layers) (lo hi : ℕ) : Prop where
  counter : lo ≤ a.counter ∧ a.counter < hi
  current : lo ≤ a.banks.current ∧ a.banks.current < hi
  header : lo ≤ a.headerBase ∧ a.headerBase+16*rows.length ≤ hi
  charges : lo ≤ a.banks.charges
  nodes : lo ≤ a.banks.nodes
  chargeEnd : ∀ i : Fin rows.length, a.banks.charges+
    2*((rows.get i).actual.first+(rows.get i).actual.count) ≤ hi
  nodeEnd : ∀ i : Fin rows.length, a.banks.nodes+
    8*((rows.get i).actual.first+(rows.get i).actual.count) ≤ hi

theorem BankInterval.stable_outside {a : NodeArchive} {rows : List Layers} {lo hi x : ℕ}
    (bank : BankInterval a rows lo hi) (outsideBank : x<lo ∨ hi≤x) : stable a rows x := by
  have ctr := bank.counter
  have cur := bank.current
  have hdr := bank.header
  have ch := bank.charges
  have nd := bank.nodes
  refine ⟨by omega, by omega, ?_, ?_⟩
  · unfold outside
    omega
  · intro i
    have ce := bank.chargeEnd i
    have ne := bank.nodeEnd i
    unfold keeps outside
    omega

theorem final_stable {W : ℕ} (a : NodeArchive) {rows : List Layers} (P : Program rows) (m : Memory W)
    {budget x : ℕ} (room : RunBounds W a rows budget) (off : stable a rows x) :
    state a P m rows.length x = m x := by
  rw [state_keeps a P m x 0 rows.length (Nat.zero_le _) le_rfl room.counterSize room.pointerSize
      (fun j _ _ => off.2.2.2 j)]
  have skip : ¬(a.headerBase ≤ x ∧ x < a.headerBase + 16*rows.length) := by
    rcases off.2.2.1 with h | h <;> omega
  simp only [state, initial, writeMemory, Fin.val_cast_of_lt room.counterSize,
    Fin.val_cast_of_lt room.pointerSize, ite_eq_right off.1, ite_eq_right off.2.1, fillSegment, ite_eq_right skip]

theorem sourceRows_of_stagePost {W K d l H M lo hi : ℕ} {A : State d l} (r : Run F A)
    (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (seed : LayerData O.layer) (a : NodeArchive) (m : Memory W)
    (ops : List Stage) (c : Cursor) (last : Layer)
    (stored : stagePost K ops c O.layer (·<lo) (natural m) H M (fun _ => False)
      (r.archiveList h C O p seed) last)
    (bank : BankInterval a (NodePublication.records (r.archiveList h C O p seed)) lo hi)
    (address : lo≤2^W) (halfCap : H≤a.halfCap) (motifCap : M≤a.motifCap)
    (seedArity : O.layer.childCount=0) :
    SourceRows a (program (r.archiveList h C O p seed)) m := by
  let xs := r.archiveList h C O p seed
  let P := program xs
  have row (i : Fin (NodePublication.records xs).length) :=
    stored.2.2 (view P i) (view_mem xs i)
  have full (i : Fin (NodePublication.records xs).length) :
      RowContents (P.data i) (·<lo) (natural m) H M :=
    ((row i).contents).resolve_left id
  refine
    { reads := fun i => (full i).reads
      bounds := ?_
      input := fun i => (full i).footprint.mono (fun _ h => bank.stable_outside (Or.inl h))
      separate := fun i => (full i).footprint.mono (fun _ h => Or.inl (h.trans_le bank.charges))
      owners := fun i => (row i).parents
      parentCells := fun i hf j => bank.stable_outside (Or.inl ((row i).ownerCells hf j))
      preceding := archive_old r h C O p seed seedArity
      halves := fun i j => ((full i).halves j).trans halfCap
      motifs := fun i hn j => ((full i).motifs hn j).trans motifCap }
  intro i
  have f := (full i).footprint.mono (fun _ h => h.trans_le address)
  exact ⟨f.child,f.halfPtr,f.width,f.motifPtr,f.copies⟩


end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
