import OAI.Computability.VPVNP.PairTerminalSelectedPrefix

/-! # The first three terminal source charges on every accepted physical trace -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords TerminalLink TerminalPrefix.Linked
open TraversalRows TraversalRoles TraversalControllerInputs DirectoryRun LocalHistory

variable {w lanes : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable (T : ℕ) (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices)

/-- Recover the *source* report lists of bootstrap, width-prefix scan and
both history-directory passes on the same five-stage trace used by the
live pair. Determinism of the empty-tape phases supplies the equalities
even when the candidate trace is described using another witness. -/
theorem selected_prefix_costs (workers : Stage → LiveProgram.PairTable) (pub : Fin 11 → Word w)
    (cap fuel base H first pitch : ℕ) (inc : IncidenceDirectory w) (starts : Word w)
    (input : Memory w) (boot : Report w) (prefixRows : List (Report w))
    (bank : workers Stage.traversalRows = ⟨_,_,TraversalController.Native.table⟩)
    (clock₂ : TraversalController.callFuel B.recordLimit+30 ≤ cap) :
    let Y := (B.execute f hf T hT X).finalState z
    let src := prefixMemory pub input boot prefixRows
    let ls := selectedLayers B f hf T hT X z
    let size := words B.recordLimit ls
    let off := size+Y.totalWidth
    let vs := executeLevels B f hf T hT X z
    let tags := selected B f hf T hT X z
    Start workers pub cap fuel Y inc starts input boot prefixRows →
    ∀ ds : (i : Fin vs.length) → LevelDirectory vs[i] src base,
      Resident pub src H first pitch off B.recordLimit base ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers vs ds) →
      (∀ j ≤ vs.length, first+j*pitch+28 ≤ base) →
      base+2*size+Y.totalWidth ≤ H → 2*tags.length*(X.positions+1) < 2^w →
      ∀ t : FiveTrace workers pub cap input,
        t.bootstrap.logs.map Prod.snd = [boot] ∧
        TerminalPrefix.Segment.Run pub Y inc starts (after input boot.events) (t.prefixRows.logs.map Prod.snd) ∧
        RAMBuckets.cost Report.probes (t.traversalRows.logs.map Prod.snd) ≤
          (2*B.recordLimit+1294)*(((S.steps+1)*T+1)*X.positions) ∧
        ∀ r ∈ t.traversalRows.logs.map Prod.snd, r.probes ≤ r.events.length ∧
          r.events.length < TraversalController.callFuel B.recordLimit := by
  intro Y src ls size off vs tags start ds resident heads below ordinal t
  obtain ⟨_,_,out,_,_,seg,cost,per,_,_,_,_,reads,_⟩ :=
    TraversalController.selected_run_with_reads B f hf T hT X z base src ds pub Y.totalWidth
      H first pitch resident heads below ordinal
  have wide : 32 ≤ 2^w := by have := resident.headerFits; omega
  obtain ⟨_,bootLogs,_,_,prefixLogs,mem⟩ := start.force t
  have cand := t.rowRun
  rw [mem] at cand
  obtain ⟨_,known,_⟩ := TraversalController.linked_stage workers pub bank seg reads clock₂ wide
    start.handoff_rows.2 (fun _ _ => rfl)
  obtain ⟨_,arenaLogs,_⟩ := known.force_quiet (fun _ h => List.eq_of_mem_replicate h) cand
  rw [bootLogs,prefixLogs,arenaLogs,stageLogs_raw,stageLogs_raw]
  exact ⟨rfl,start.rawScan,cost,per⟩

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
