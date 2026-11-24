import OAI.Computability.VPVNP.PairSimulationTerminalBlocks
import OAI.Computability.VPVNP.PairSimulationTerminalTraceEquiv
import OAI.Computability.VPVNP.PairSimulationTerminalPhaseBuild
import OAI.Computability.VPVNP.PairSimulationTraceJobs

/-!
# Terminal payloads and site witnesses in the five native phases

The three setup blocks are forced by their empty choice tapes. A shared
payload therefore selects exactly one fourth block and determines the memory
for the last block. Independent site witnesses in that selected payload
classify the final vertex block. The resulting path has the unabridged five
streams and all of their physical reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink
open BurstRAM LiveProgram NetworkKernel LocalHistory CompressorRecords

variable {w : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w} {cap : ℕ}

private theorem quiet_block {e m} (known : CompletedPhase workers pub cap e m)
    (quiet : ∀ b ∈ known.val.choices, b=[]) (other : Block w)
    (phase : Phase workers pub cap e m other.choices other.logs other.memory) : other = known.val := by
  obtain ⟨choices,logs,memory⟩ := known.prop.force_quiet quiet phase
  cases known with | mk known _ =>
    cases known
    cases other
    simp_all only

variable {m : Memory w}

private theorem trace_injective (q : QuietPrefix workers pub cap m) :
    Function.Injective (fun x : Σ a : q.BitPaths, q.VertexPaths a => q.trace x.1 x.2) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ eq
  have ab : a=b := Subtype.ext (congrArg FiveTrace.sharedBits eq)
  subst b
  exact congrArg (Sigma.mk a) (Subtype.ext (congrArg FiveTrace.vertices eq))

private theorem trace_surjective (q : QuietPrefix workers pub cap m) :
    Function.Surjective (fun x : Σ a : q.BitPaths, q.VertexPaths a => q.trace x.1 x.2) := by
  rintro ⟨u,v,z,b,x,hu,hv,hz,hb,hx⟩
  obtain rfl := quiet_block q.boot q.bootQuiet u hu
  obtain rfl := quiet_block q.prefixRows q.prefixQuiet v hv
  obtain rfl := quiet_block q.traversalRows q.traversalQuiet z hz
  exact ⟨⟨⟨b,hb⟩,⟨x,hx⟩⟩,rfl⟩

/-- Every accepting terminal trace consists of the three known blocks
followed by two independently classified blocks, with dependent memory. -/
noncomputable def QuietPrefix.blocksEquiv (q : QuietPrefix workers pub cap m) :
    (Σ a : q.BitPaths, q.VertexPaths a) ≃ FiveTrace workers pub cap m :=
  Equiv.ofBijective (fun x => q.trace x.1 x.2) ⟨trace_injective q,trace_surjective q⟩

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {N : Network}
variable {sc : ScanPhase N} {P : SiteParsers κ N} (q : QuietPrefix workers pub cap m)
variable (bits : sc.Path ≃ q.BitPaths)
variable (jobs : ∀ a : sc.Path,
  (∀ v, (P.witnesses v (WireTensor.edgeAssignment N.src N.dst (sc.payload a) v)).Choice) ≃ q.VertexPaths (bits a))

/-- Each shared arc assignment and its site jobs give the five actual
physical blocks, and every five-block trace recovers this data. -/
noncomputable def QuietPrefix.dataTrace : TerminalData sc P ≃ FiveTrace workers pub cap m :=
  let split : TerminalData sc P ≃ (Σ a : sc.Path,
    ∀ v, (P.witnesses v (WireTensor.edgeAssignment N.src N.dst (sc.payload a) v)).Choice) :=
    ⟨fun x => ⟨x.arcs,x.choices⟩, fun x => ⟨x.1,x.2⟩, fun _ => rfl, fun _ => rfl⟩
  split.trans ((Equiv.sigmaCongr (β₂ := q.VertexPaths) bits jobs).trans q.blocksEquiv)

theorem QuietPrefix.dataTrace_eq (x : TerminalData sc P) :
    q.dataTrace bits jobs x = q.trace (bits x.arcs) (jobs x.arcs x.choices) := rfl

/-- The five-stage source program counts the actual shared arc and vertex
witnesses, with an arbitrary cap that holds for every produced trace. -/
noncomputable def QuietPrefix.dataPaths (fit : 32 ≤ 2^w) (enough : 26 ≤ cap)
    (ok : List (Report w) → Prop)
    (bounded : ∀ x : TerminalData sc P, ok (reports (header pub) (q.dataTrace bits jobs x).logs)) :
    TerminalData sc P ≃ ActualPaths (program workers pub) cap 0 m ok :=
  let e := q.dataTrace bits jobs
  let restrict : FiveTrace workers pub cap m ≃ {t : FiveTrace workers pub cap m // ok (reports (header pub) t.logs)} :=
    (Equiv.subtypeUnivEquiv (fun t => by obtain ⟨x,rfl⟩ := e.surjective t; exact bounded x)).symm
  e.trans (restrict.trans (fiveTraceEquiv workers pub cap m ok fit enough))

theorem QuietPrefix.dataPaths_tapes (fit : 32 ≤ 2^w) (enough : 26 ≤ cap) (ok : List (Report w) → Prop)
    (bounded : ∀ x : TerminalData sc P, ok (reports (header pub) (q.dataTrace bits jobs x).logs))
    (x : TerminalData sc P) :
    (q.dataPaths bits jobs fit enough ok bounded x).val =
      (q.trace (bits x.arcs) (jobs x.arcs x.choices)).choices := rfl

theorem FiveTrace.after_reports (t : FiveTrace workers pub cap m) :
    after m (eventLog (reports (header pub) t.logs)) = t.vertices.memory := by
  have join (mem : Memory w) (x y : List (Log w)) :
      after mem (eventLog (reports (header pub) (x++y))) =
        after (after mem (eventLog (reports (header pub) x))) (eventLog (reports (header pub) y)) := by
    simp only [reports,List.map_append,eventLog,List.flatMap_append,after,List.foldl_append]
  rw [FiveTrace.logs,join,t.bootRun.final_memory,join,t.prefixRun.final_memory,join,t.rowRun.final_memory,
    join,t.bitRun.final_memory,t.vertexRun.final_memory]

theorem QuietPrefix.dataPaths_logs (fit : 32 ≤ 2^w) (enough : 26 ≤ cap) (ok : List (Report w) → Prop)
    (bounded : ∀ x : TerminalData sc P, ok (reports (header pub) (q.dataTrace bits jobs x).logs))
    (x : TerminalData sc P) :
    (q.dataPaths bits jobs fit enough ok bounded x).property.choose =
      reports (header pub) (q.trace (bits x.arcs) (jobs x.arcs x.choices)).logs := by
  let tr := q.trace (bits x.arcs) (jobs x.arcs x.choices)
  have actual := (q.dataPaths bits jobs fit enough ok bounded x).property.choose_spec.1
  apply Option.some.inj (actual.symm.trans _)
  exact tr.visits.native workers pub cap fit enough (by rintro e he; cases he; trivial)

theorem QuietPrefix.dataPaths_after (fit : 32 ≤ 2^w) (enough : 26 ≤ cap) (ok : List (Report w) → Prop)
    (bounded : ∀ x : TerminalData sc P, ok (reports (header pub) (q.dataTrace bits jobs x).logs))
    (x : TerminalData sc P) :
    after m (eventLog (q.dataPaths bits jobs fit enough ok bounded x).property.choose) =
      (jobs x.arcs x.choices).val.memory := by
  rw [dataPaths_logs]
  exact FiveTrace.after_reports _

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
