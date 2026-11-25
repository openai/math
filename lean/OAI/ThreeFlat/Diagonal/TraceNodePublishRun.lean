import OAI.ThreeFlat.Diagonal.TraceNodeHeaderMount
import OAI.ThreeFlat.Diagonal.TraceNodeJournalSource
import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveChargeRun

namespace OAI
/-! # Running the native compactor and publishing its terminal work and parent columns -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure PhysicalStage
open NavigationDirectory TraceNodeHeaders
open scoped Fin.CommRing Classical
noncomputable section
variable {F : Type} [Field F] {W : ℕ}

/-- Every output word agrees with the chronological node pass using its compacted physical headers. -/
theorem publish_compact_run {K ctrl head budget : ℕ} (a : NodeArchive) (m : Memory W)
    (ops : List Stage) (c : Cursor) (seed : Layer) {rows : List Layers} (P : Program rows)
    (headers : rows=nodeLayers K ops c seed)
    (sroom : ScanRoom W ctrl head c.header a.headerBase ops.length)
    (pointer : (m ctrl).val=head)
    (fields : ∀ j<13,(m (head+j)).val=scanFields a.banks ops.length c.header a.headerBase seed j)
    (mounted : MountedAt (natural m) K ops c) (live : ∀ op∈ops,0<successors op)
    (room : RunBounds W a rows budget) (ready : ∀ i, bodyReady a P m i) :
    (compactPublish W ctrl a rows.length).Spec (·=m) (fun _ out=>out=state a P m rows.length)
      (compactTicks ctrl rows.length budget) := by
  let mountedMem:=fillSegment a.headerBase (16*rows.length) (tapeWord a rows) m
  let pointing:=writeMemory mountedMem (a.banks.current:Word W) (a.headerBase:Word W)
  have first : (compactScan W ctrl).Spec (·=m) (fun _ out => out=mountedMem)
      (11+16*rows.length*(2*(compactRow ctrl).work+4)) := by
    dsimp only [mountedMem]
    rw [headers]
    exact compactScan_spec a ops c seed m sroom pointer fields mounted live
  have pointerSet : (start (a.banks.current:Word W) (a.headerBase:Word W)).Spec
      (·=mountedMem) (fun _ out=>out=pointing) 3 :=
    Procedure.Spec.atMemory (start_spec _ _) mountedMem trivial
  have counterSet : (start (a.counter:Word W) (rows.length:Word W)).Spec
      (·=pointing) (fun _ out=>out=initial a rows m) 3 :=
    Procedure.Spec.atMemory (start_spec _ _) pointing trivial
  intro labels regs slots
  refine Procedure.Spec.mono
    (Procedure.Spec.seq first
      (Procedure.Spec.seq pointerSet
        (Procedure.Spec.seq counterSet (counted_run a P m room ready) (fun _ _ out=>out))
        (fun _ _ out=>out))
      (fun _ _ out=>out)) (fun _ h=>h) ?_ le_rfl
  rintro _ _ ⟨_,_,_,_,_,_,out⟩
  exact out

/-- The resource registrar reads each final site's charged work directly from the emitted columns.
Only the geometrically allocated bank interval changes; all public and per-stage owner cells outside survive. -/
theorem publish_selected {K ctrl head budget lo hi d l H M : ℕ} {A : State d l}
    (r : Run F A) (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites)
    (p : r.ArchivePath h C O) (seed : LayerData O.layer) (a : NodeArchive) (mem : Memory W)
    (ops : List Stage) (c : Cursor) (last : Layer)
    (sroom : ScanRoom W ctrl head c.header a.headerBase ops.length)
    (pointer : (mem ctrl).val=head)
    (fields : ∀ j<13,(mem (head+j)).val=scanFields a.banks ops.length c.header a.headerBase O.layer j)
    (mounted : MountedAt (natural mem) K ops c) (live : ∀ op∈ops,0<successors op)
    (seen : TraceRecovery.stagePost K ops c O.layer (·<lo) (natural mem) H M (fun _=>False)
      (r.archiveList h C O p seed) last)
    (bank : BankInterval a (records (r.archiveList h C O p seed)) lo hi)
    (address : lo≤2^W) (halfCap : H≤a.halfCap) (motifCap : M≤a.motifCap)
    (seedArity : O.layer.childCount=0)
    (room : RunBounds W a (records (r.archiveList h C O p seed)) budget)
    (tape : TapeBounds W a (records (r.archiveList h C O p seed)))
    (start pay : A.Site→ℕ) (seeds : State.SeedRows O seed a.banks start pay)
    (fit : r.ArchiveFits W a.banks.unitWork h C start pay) :
    let xs:=r.archiveList h C O p seed
    let n:=(records xs).length
    (compactPublish W ctrl a n).Spec (·=mem) (fun _ out =>
      out=state a (program xs) mem n ∧
      (∀ z, z<lo ∨ hi≤z → out z=mem z) ∧
      O.Charged a.banks (natural out) start pay ∧ r.ArchiveRowsStored a.banks (natural out) h C O p ∧
      ∀ v : (r.plan.finish h).Site,
        let terminal:=r.finalArchive h C O p
        let id:=terminal.1.first+(terminal.2 ((r.finalSite h).symm v)).val
        (out (a.banks.charges+2*id)).val=a.banks.unitWork*r.chargeAt h C start v)
      (compactTicks ctrl n budget) := by
  let xs:=r.archiveList h C O p seed
  have src:=sourceRows_of_stagePost r h C O p seed a mem ops c last seen bank address halfCap motifCap seedArity
  have all:=archive_charge_fits r h C O p seed a mem room start pay seeds fit
  have good:=ready_of_source a (program xs) mem room tape src (fun i j=>all i j 1)
  have stored:=archive_rows_stored r h C O p seed a mem room src.preceding all
      (archive_parent_fits r h C O p seed a room)
  dsimp only
  intro labels regs slots
  refine Procedure.Spec.mono
    (publish_compact_run a mem ops c O.layer (program xs) seen.1
      sroom pointer fields mounted live room good) (fun _ h=>h) ?_ le_rfl
  rintro _ out rfl
  let charged:=seeds.charged _ stored.1
  refine ⟨rfl,fun z outside => final_stable _ _ _ room (bank.stable_outside outside),
    charged,stored.2,?_⟩
  intro v
  have work:=(r.archive_charges h C O p a.banks _ stored.2 start pay charged v).1
  simpa only [archiveColumn,Fin.val_zero,Nat.add_zero,natural] using work


end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
