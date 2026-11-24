import OAI.Computability.VPVNP.PairSimulationWorkerControl
import OAI.Computability.VPVNP.LiveDeterministicReachable

/-!
# Physical terminal frames on partial nondeterministic paths

A successful shared-bit call can return to its worker or finish that phase.
At a finishing call, the already traversed prefix and the last report form a
completed fourth block. Its actual final memory initializes the vertex phase.
A later rejecting vertex has no effect on this classification of the prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink
open BurstRAM LiveProgram CompressorRecords
variable {w : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w} {cap : ℕ}

/-- Every completion from the current fourth-stage state can be prepended
by the actual successful earlier calls of this same stage. -/
private def BitPrefix (workers : Stage → PairTable) (pub : Fin 11 → Word w) (cap : ℕ) (initial : Memory w)
    (st : Word w) (m : Memory w) := ∀ {bs ls final},
    Phase workers pub cap (.resume Stage.sharedBits st) m bs ls final →
    ∃ bs' ls', Phase workers pub cap (.resume Stage.sharedBits 0) initial bs' ls' final

private theorem BitPrefix.start (m : Memory w) : BitPrefix workers pub cap m 0 m :=
  fun {_ _ _} h => ⟨_,_,h⟩

private theorem BitPrefix.continue {initial m : Memory w} {st st' : Word w} {b : List Bool} {r : Report w}
    (earlier : BitPrefix workers pub cap initial st m)
    (call : execute (source workers Stage.sharedBits pub) (rawFuel pub cap (.resume Stage.sharedBits st))
      ((source workers Stage.sharedBits pub).start st) m b = some r)
    (room : (exitReport (header pub) Stage.sharedBits r).events.length < rawFuel pub cap (.resume Stage.sharedBits st))
    (cont : r.result = some st') :
    BitPrefix workers pub cap initial st' (after m (report (header pub) (.resume Stage.sharedBits st) r).events) :=
  fun {_ _ _} h => earlier (Phase.more call room cont h)

private theorem BitPrefix.finish {initial m : Memory w} {st : Word w} {b : List Bool} {r : Report w}
    (earlier : BitPrefix workers pub cap initial st m)
    (call : execute (source workers Stage.sharedBits pub) (rawFuel pub cap (.resume Stage.sharedBits st))
      ((source workers Stage.sharedBits pub).start st) m b = some r)
    (room : (exitReport (header pub) Stage.sharedBits r).events.length < rawFuel pub cap (.resume Stage.sharedBits st))
    (halt : r.result = none) :
    ∃ q : CompletedPhase workers pub cap (.resume Stage.sharedBits 0) initial,
      q.val.memory = after m (report (header pub) (.resume Stage.sharedBits st) r).events := by
  obtain ⟨choices,logs,ph⟩ := earlier (Phase.last call room halt)
  exact ⟨⟨⟨choices,logs,_⟩,ph⟩,rfl⟩

variable {a : ℕ} {initial : Memory w} (bit : WorkerControl workers pub cap Stage.sharedBits a initial)
variable (vertex : ∀ q : CompletedPhase workers pub cap (.resume Stage.sharedBits 0) initial,
  WorkerControl workers pub cap Stage.vertices a q.val.memory)

private inductive Progress : Entry w → Memory w → Prop
  | bits {st mem} : bit.inv st mem → BitPrefix workers pub cap initial st mem →
      Progress (.resume Stage.sharedBits st) mem
  | site (q : CompletedPhase workers pub cap (.resume Stage.sharedBits 0) initial) {st mem} :
      (vertex q).inv st mem → Progress (.resume Stage.vertices st) mem

private theorem follow_return (e : Entry w) (raw : Report w) {x : Word w} (h : raw.result = some x) :
    e.follow raw = some (.resume e.stage x) := by simp [Entry.follow,target,h]

private theorem next_live {e j : Entry w} {raw : Report w} {m : Memory w} (fit : 32 ≤ 2^w)
    (h : e.follow raw = some j) :
    j.Valid (header pub) (after m (report (header pub) e raw).events) := next_valid _ _ _ _ _ fit h

private theorem progress_step {e : Entry w} {m : Memory w} (fit : 32 ≤ 2^w) (hcap : 26 ≤ cap)
    (h : Progress bit vertex e m) (valid : e.Valid (header pub) m) {bs out}
    (run : execute (program workers pub) cap ((program workers pub).start e.marker) m bs = some out) :
    after m out.events a = m a ∧ ∀ st', out.result = some st' →
      ∃ j : Entry w, j.marker = st' ∧ j.Valid (header pub) (after m out.events) ∧
        Progress bit vertex j (after m out.events) := by
  obtain ⟨r,call,room,rfl⟩ := (recover_call workers pub cap e m bs (by omega) hcap valid out).mp run
  cases h with
  | @bits st mem inv prefix₀ =>
    obtain ⟨frame,advance⟩ := bit.advance st m bs r inv call
    refine ⟨frame,?_⟩
    intro st' returned
    cases rr : r.result with
    | some y =>
      have h := follow_return (.resume Stage.sharedBits st) r rr
      rw [report_result,h] at returned
      obtain rfl := Option.some.inj returned
      exact ⟨_,rfl,next_live fit h,.bits (advance y rr) (prefix₀.continue call room rr)⟩
    | none =>
      have h : (Entry.resume Stage.sharedBits st).follow r = some (.resume Stage.vertices 0) := by
        simp only [Entry.follow,Entry.stage,target,rr]
        rfl
      rw [report_result,h] at returned
      obtain rfl := Option.some.inj returned
      obtain ⟨q,hq⟩ := prefix₀.finish call room rr
      exact ⟨_,rfl,next_live fit h,.site q (hq ▸ (vertex q).ready)⟩
  | @site q st mem inv =>
    obtain ⟨frame,advance⟩ := (vertex q).advance st m bs r inv call
    refine ⟨frame,?_⟩
    intro st' returned
    cases rr : r.result with
    | some y =>
      have h := follow_return (.resume Stage.vertices st) r rr
      rw [report_result,h] at returned
      obtain rfl := Option.some.inj returned
      exact ⟨_,rfl,next_live fit h,.site q (advance y rr)⟩
    | none =>
      have h : (Entry.resume Stage.vertices st).follow r = none := by simp only [Entry.follow,Entry.stage,target,rr]; rfl
      rw [report_result,h] at returned
      contradiction

include bit vertex in
/-- Every successful report, including the terminal accepting exit, on
every reached physical prefix from the shared-bit entry preserves the word.
The statement places no requirement on whether a later burst will accept. -/
theorem shared_vertices_safe (fit : 32 ≤ 2^w) (hcap : 26 ≤ cap)
    (valid : (Entry.resume Stage.sharedBits (0 : Word w)).Valid (header pub) initial) :
    ∀ {st mem bs out}, Reached (program workers pub) cap (Entry.resume Stage.sharedBits (0 : Word w)).marker initial st mem →
      execute (program workers pub) cap ((program workers pub).start st) mem bs = some out →
      after mem out.events a = mem a := by
  have inv {st mem} (reach : Reached (program workers pub) cap (Entry.resume Stage.sharedBits (0 : Word w)).marker initial st mem) :
      ∃ e : Entry w, e.marker = st ∧ e.Valid (header pub) mem ∧ Progress bit vertex e mem := by
    induction reach with
    | start => exact ⟨_,rfl,valid,.bits bit.ready (BitPrefix.start _)⟩
    | more prev run cont ih =>
      obtain ⟨e,rfl,hvalid,progress⟩ := ih
      exact (progress_step bit vertex fit hcap progress hvalid run).2 _ cont
  intro st mem bs out reach run
  obtain ⟨e,rfl,hvalid,progress⟩ := inv reach
  exact (progress_step bit vertex fit hcap progress hvalid run).1

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
