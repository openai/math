import OAI.Computability.VPVNP.PairSimulationTerminalSplit

/-!
# The five terminal segments in every accepting pair traversal

An accepting path splits at the unique first accepting exit of each worker.
Conversely, the five completed physical segments join with the original
choice strings in their original order. No normalization or padding of
branch strings occurs at the stage boundaries.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM LiveProgram

variable {w : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w} {cap : ℕ}

theorem Phase.append_visits {e m bs ls final} (h : Phase workers pub cap e m bs ls final)
    {more rest} (tail : Visits workers pub cap (handoff e.stage) final more rest) :
    Visits workers pub cap (some e) m (bs++more) (ls++rest) := by
  induction h with
  | @last e m b raw call room accepted =>
    have step : e.follow raw = handoff e.stage := by
      cases hn : next e.stage <;> simp [Entry.follow,target,accepted,handoff,hn]
    exact .cons call room (step ▸ tail)
  | @more e m b bs raw x ls final call room returned _ ih =>
    have step : e.follow raw = some (.resume e.stage x) := by simp [Entry.follow,target,returned]
    exact .cons call room (step ▸ ih tail)

theorem Phase.finish_append {e m bs ls final} (h : Phase workers pub cap e m bs ls final)
    (rest : List (Log w)) : finish (some e) (ls++rest) = finish (handoff e.stage) rest := by
  induction h with
  | @last e m b raw call room accepted =>
    cases hn : next e.stage <;> simp [finish,Entry.follow,target,accepted,handoff,hn]
  | @more e m b bs raw x ls final call room returned _ ih =>
    simpa only [List.cons_append,finish,Entry.follow,target,returned,Option.map_some,Entry.stage] using ih

/-- The private choices, worker reports and physical exit memory of one stage. -/
structure Block (w : ℕ) where
  /-- Ordered private choice stream for each call of this stage. -/
  choices : List (List Bool)
  /-- Entry and original worker report for each call. -/
  logs : List (Log w)
  /-- Physical memory after the final call of the stage. -/
  memory : Memory w

/-- The five completed native worker phases and their consecutive physical memories. -/
structure FiveTrace (workers : Stage → PairTable) (pub : Fin 11 → Word w) (cap : ℕ) (initialMemory : Memory w) where
  /-- Trace of the terminal-header setup. -/
  bootstrap : Block w
  /-- Trace of the final width-prefix scan. -/
  prefixRows : Block w
  /-- Trace of the traversal-row and role-tag construction. -/
  traversalRows : Block w
  /-- Trace of the shared wire-bit scan. -/
  sharedBits : Block w
  /-- Trace of the ascending vertex calls and final ordinal check. -/
  vertices : Block w
  bootRun : Phase workers pub cap .initial initialMemory bootstrap.choices bootstrap.logs bootstrap.memory
  prefixRun : Phase workers pub cap (.resume Stage.prefixRows 0) bootstrap.memory prefixRows.choices prefixRows.logs prefixRows.memory
  rowRun : Phase workers pub cap (.resume Stage.traversalRows 0) prefixRows.memory traversalRows.choices traversalRows.logs traversalRows.memory
  bitRun : Phase workers pub cap (.resume Stage.sharedBits 0) traversalRows.memory sharedBits.choices sharedBits.logs sharedBits.memory
  vertexRun : Phase workers pub cap (.resume Stage.vertices 0) sharedBits.memory vertices.choices vertices.logs vertices.memory

variable {m : Memory w}

/-- All call choice strings in physical order. -/
def FiveTrace.choices (t : FiveTrace workers pub cap m) :=
  t.bootstrap.choices ++ (t.prefixRows.choices ++ (t.traversalRows.choices ++ (t.sharedBits.choices ++ t.vertices.choices)))

/-- All tagged worker reports in physical order. -/
def FiveTrace.logs (t : FiveTrace workers pub cap m) :=
  t.bootstrap.logs ++ (t.prefixRows.logs ++ (t.traversalRows.logs ++ (t.sharedBits.logs ++ t.vertices.logs)))

theorem FiveTrace.visits (t : FiveTrace workers pub cap m) :
    Visits workers pub cap (some .initial) m t.choices t.logs := by
  apply t.bootRun.append_visits
  apply t.prefixRun.append_visits
  apply t.rowRun.append_visits
  apply t.bitRun.append_visits
  change Visits workers pub cap (some (.resume Stage.vertices 0)) _ _ _
  simpa only [List.append_nil] using t.vertexRun.append_visits (.nil _ _)

theorem FiveTrace.closed (t : FiveTrace workers pub cap m) : finish (some .initial) t.logs = none := by
  unfold FiveTrace.logs
  rw [t.bootRun.finish_append]
  change finish (some (.resume Stage.prefixRows 0)) _ = none
  rw [t.prefixRun.finish_append]
  change finish (some (.resume Stage.traversalRows 0)) _ = none
  rw [t.rowRun.finish_append]
  change finish (some (.resume Stage.sharedBits 0)) _ = none
  rw [t.bitRun.finish_append]
  change finish (some (.resume Stage.vertices 0)) _ = none
  have last : handoff (w := w) Stage.vertices = none := rfl
  simpa only [List.append_nil,Entry.stage,last,finish] using t.vertexRun.finish_append []

theorem recover_five {bs : List (List Bool)} {ls : List (Log w)}
    (h : Visits workers pub cap (some .initial) m bs ls) (closed : finish (some .initial) ls = none) :
    ∃ t : FiveTrace workers pub cap m, bs = t.choices ∧ ls = t.logs := by
  obtain ⟨b0,bs1,r0,rs1,m1,hb0,hr0,p0,v1,c1⟩ := split_stage workers pub cap .initial m bs ls h closed
  obtain ⟨b1,bs2,r1,rs2,m2,hb1,hr1,p1,v2,c2⟩ :=
    split_stage workers pub cap (.resume Stage.prefixRows 0) m1 bs1 rs1 v1 c1
  obtain ⟨b2,bs3,r2,rs3,m3,hb2,hr2,p2,v3,c3⟩ :=
    split_stage workers pub cap (.resume Stage.traversalRows 0) m2 bs2 rs2 v2 c2
  obtain ⟨b3,bs4,r3,rs4,m4,hb3,hr3,p3,v4,c4⟩ :=
    split_stage workers pub cap (.resume Stage.sharedBits 0) m3 bs3 rs3 v3 c3
  obtain ⟨b4,bs5,r4,rs5,m5,hb4,hr4,p4,v5,_⟩ :=
    split_stage workers pub cap (.resume Stage.vertices 0) m4 bs4 rs4 v4 c4
  change Visits workers pub cap none m5 bs5 rs5 at v5
  cases v5
  refine ⟨⟨⟨b0,r0,m1⟩,⟨b1,r1,m2⟩,⟨b2,r2,m3⟩,⟨b3,r3,m4⟩,⟨b4,r4,m5⟩,p0,p1,p2,p3,p4⟩,
    by simp [FiveTrace.choices,hb0,hb1,hb2,hb3,hb4],
    by simp [FiveTrace.logs,hr0,hr1,hr2,hr3,hr4]⟩

/-- A physical accepted branch string has all five completed stage runs.
Its cap applies to the physical reports after dispatch and handoff. -/
theorem accepts_five (workers : Stage → PairTable) (pub : Fin 11 → Word w) (cap : ℕ)
    (m : Memory w) (bs : List (List Bool)) (ok : List (Report w) → Prop) (fit : 32 ≤ 2^w) (hcap : 26 ≤ cap) :
    (∃ rs, runSegment (program workers pub) cap (some 0) m bs = some rs ∧ endState (some 0) rs = none ∧ ok rs) ↔
      ∃ t : FiveTrace workers pub cap m, bs = t.choices ∧ ok (reports (header pub) t.logs) := by
  rw [actual_iff workers pub cap m bs ok fit hcap]
  constructor
  · rintro ⟨ls,visits,closed,approved⟩
    obtain ⟨t,he,rfl⟩ := recover_five visits closed
    exact ⟨t,he,approved⟩
  · rintro ⟨t,rfl,approved⟩
    exact ⟨_,t.visits,t.closed,approved⟩

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
