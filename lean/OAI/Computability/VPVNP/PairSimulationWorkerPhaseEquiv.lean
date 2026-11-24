import OAI.Computability.VPVNP.PairSimulationTerminalBlocks
import OAI.Computability.VPVNP.PairSimulationTerminalPhaseBuild
import OAI.Computability.VPVNP.PairSimulationTerminalTraceEquiv
import OAI.Computability.VPVNP.CompressorOnlineWorkerInversion

/-!
# Relocating all accepted source worker paths to their terminal phase

The source executes on memory agreeing with the physical bank away from the
two terminal controller cells. Known paths replay forward after the clock is
reduced by the dispatch allowance. Conversely every completed physical block
can be recovered at the full source clock. The chosen memory readback agrees
at every worker address, including the dense histogram.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink
open BurstRAM LiveProgram CompressorRecords

private theorem reclock {w f g : ℕ} {K : Type*} {P : BurstRAM.Program w K} {s : Option (Word w)} {m : Memory w}
    {bs : List (List Bool)} {rs : List (Report w)}
    (h : runSegment P f s m bs = some rs) (room : ∀ r ∈ rs, r.events.length < g) :
    runSegment P g s m bs = some rs := by
  induction bs generalizing s m rs with
  | nil => exact h
  | cons b bs ih =>
    cases s with
    | none => contradiction
    | some st =>
      cases run : execute P f (P.start st) m b with
      | none => simp [runSegment,run] at h
      | some r =>
        simp only [runSegment,run,Option.map_eq_some_iff] at h
        obtain ⟨tail,ht,rfl⟩ := h
        obtain ⟨hr,rest⟩ := List.forall_mem_cons.mp room
        simp only [runSegment,execute_at_cap run hr,ih ht rest,Option.map_some]

variable {w : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w} {cap : ℕ}
variable {e : Entry w} {src phy : Memory w}

/-- Obligations for the actual worker reports under the terminal controller. -/
structure WorkerFrame (workers : Stage → PairTable) (pub : Fin 11 → Word w) (cap : ℕ)
    (e : Entry w) (src phy : Memory w) where
  clock : 30 ≤ cap
  agree : SourceTransport.Agree (workerCell (header pub)) src phy
  sourceReads : ∀ p : ActualPaths (source workers e.stage pub) cap e.state src (fun _ => True),
    SourceTransport.Reads (workerCell (header pub)) (eventLog p.property.choose)
  sourceRoom : ∀ p : ActualPaths (source workers e.stage pub) cap e.state src (fun _ => True),
    ∀ r ∈ p.property.choose, r.events.length < cap-30
  phaseReads : ∀ q : CompletedPhase workers pub cap e phy,
    SourceTransport.Reads (workerCell (header pub)) (eventLog (q.val.logs.map Prod.snd))

namespace WorkerFrame
variable (F : WorkerFrame workers pub cap e src phy)

/-- Transport a completed source-worker path to a physical terminal phase, adding the
controller reports and computing the resulting physical memory from their events. -/
noncomputable def block (p : ActualPaths (source workers e.stage pub) cap e.state src (fun _ => True)) :
    CompletedPhase workers pub cap e phy :=
  let rs := p.property.choose
  ⟨⟨p.val,stageLogs e rs,after phy (eventLog (stageReports (header pub) e rs))⟩,
    closed_phase workers pub (cap-30) cap e src phy p.val rs (Nat.sub_add_cancel F.clock).le F.agree
      (F.sourceReads p) (reclock p.property.choose_spec.1 (F.sourceRoom p)) p.property.choose_spec.2.1⟩

/-- All actual physical completions, including arbitrary incoming tape
lengths, are obtained from the original worker at the selected memory. -/
noncomputable def sourceBlockEquiv :
    ActualPaths (source workers e.stage pub) cap e.state src (fun _ => True) ≃ CompletedPhase workers pub cap e phy :=
  Equiv.ofBijective F.block ⟨fun _ _ h => Subtype.ext (congrArg (fun q => q.val.choices) h),by
    intro q
    obtain ⟨hr,hh,_⟩ := q.prop.source_segment workers pub cap src F.agree (F.phaseReads q)
    let p : ActualPaths (source workers e.stage pub) cap e.state src (fun _ => True) :=
      ⟨q.val.choices,q.val.logs.map Prod.snd,hr,hh,trivial⟩
    refine ⟨p,Subtype.ext ?_⟩
    exact ((F.block p).prop.block_eq_suffix q.prop (a := []) (b := []) rfl).1⟩

theorem sourceBlock_choices (p : ActualPaths (source workers e.stage pub) cap e.state src (fun _ => True)) :
    (F.sourceBlockEquiv p).val.choices = p.val := rfl

theorem sourceBlock_reports (p : ActualPaths (source workers e.stage pub) cap e.state src (fun _ => True)) :
    (F.sourceBlockEquiv p).val.logs = stageLogs e p.property.choose := rfl

theorem sourceBlock_memory (p : ActualPaths (source workers e.stage pub) cap e.state src (fun _ => True)) :
    SourceTransport.Agree (workerCell (header pub)) (after src (eventLog p.property.choose))
      (F.sourceBlockEquiv p).val.memory := by
  let q := F.sourceBlockEquiv p
  have h := (q.prop.source_segment workers pub cap src F.agree (F.phaseReads q)).2.2
  simpa only [q,sourceBlock_reports,stageLogs_raw] using h

end WorkerFrame
end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
