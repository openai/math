import OAI.Computability.VPVNP.CompressorPassIntervalData
import OAI.Computability.VPVNP.CompressorExecutionTrace

/-! # Prepending the four deterministic cursor rows to selected compressor traces

The choice of each later pass is retained. The physical path predicate is
evaluated on all reports, including the initial deterministic rows. The
small-clock core report lists and the accepting path's actual bit stream
are preserved by the same concatenation.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace.QuietInterval

open BurstRAM Compression BlockPlanner BranchSegments

variable {w cap small : ℕ} {script : Script} {pub : Fin 11 → Word w}
  {st : Option (Word w)} {m : Memory w}
  (initial : QuietInterval script pub cap small st m)
  {R : Type*} [CommSemiring R] {a g b n : ℕ} {X : State a g}
  {E : StateExecution R b n X}
  (t : ExecutionTrace (OnlineWorkspace.program script.plan pub) (cap+24) E initial.segment.state initial.segment.memory)

/-- The deterministic cursor prefix followed by the selected compression passes. -/
def withTrace : Cut (OnlineWorkspace.program script.plan pub) (cap+24) st m E.Choices :=
  Cut.before initial.segment initial.segment.bits.length initial.quiet t.cut

theorem withTrace_frame (h : t.Framed ((pub 2).val+6)) :
    (withTrace initial t).PrefixFrame ((pub 2).val+6) :=
  Cut.PrefixFrame.before initial.segment initial.segment.bits.length initial.quiet initial.stable h.cut

theorem withTrace_stopped (z : E.Choices) : ((withTrace initial t).part z).state = none :=
  (initial.segment.append_state _).trans (t.stopped z)

theorem withTrace_memory (z : E.Choices) : ((withTrace initial t).part z).memory = (t.cut.part z).memory :=
  initial.segment.append_memory _

/-- The operand-room predicate belongs to the whole run and can depend
on the reports of both the forced prefix and the selected suffix. -/
def accepted (allow : List (Report w) → Prop) :
    {z : E.Choices // allow (initial.segment.logs ++ (t.cut.part z).logs)} ≃
      LiveProgram.PathsFrom (OnlineWorkspace.program script.plan pub) (cap+24) st m allow :=
  (t.acceptedEquiv fun rs => allow (initial.segment.logs++rs)).trans
    (LiveProgram.emptySegmentEquiv (initial.quiet ▸ initial.segment.run) allow)

/-- Bijection with all selected terms when every branch meets the whole-run predicate. -/
def allAccepted (allow : List (Report w) → Prop)
    (allowed : ∀ z, allow (initial.segment.logs++(t.cut.part z).logs)) :
    E.Choices ≃ LiveProgram.PathsFrom (OnlineWorkspace.program script.plan pub) (cap+24) st m allow :=
  (Equiv.subtypeUnivEquiv allowed).symm.trans (accepted initial t allow)

theorem allAccepted_bits (allow : List (Report w) → Prop)
    (allowed : ∀ z, allow (initial.segment.logs++(t.cut.part z).logs)) (z : E.Choices) :
    ((allAccepted initial t allow allowed) z).val = initial.segment.bits++(t.cut.part z).bits := by
  change List.replicate initial.segment.bits.length [] ++ (t.cut.part z).bits = _
  rw [← initial.quiet]

/-- Any finite successful call prefix through these rows and the recursive
timeline retains all six bank words and the preceding live header. -/
theorem withTrace_stable (frame : t.Framed ((pub 2).val+6)) {bs rs}
    (run : runSegment (OnlineWorkspace.program script.plan pub) (cap+24) st m bs = some rs) :
    SourceBankFrame.Stable ((pub 2).val+6) m rs := by
  rcases Cut.deterministic_prefix initial.segment initial.segment.bits.length initial.quiet initial.stable run with h | ⟨tail,rfl⟩
  · exact h
  · rw [PrimedSchedule.runSegment_append,initial.segment.run] at run
    change (runSegment _ _ initial.segment.state initial.segment.memory tail).map _ = some rs at run
    obtain ⟨xs,done,rfl⟩ := Option.map_eq_some_iff.mp run
    exact initial.stable.append (frame.stable done)

/-- Small-clock inner reports of both the forced cursor interval and the selected tail. -/
def combinedCore (core : ∀ z, OnlineWorkspace.Core script pub (t.cut.part z) small) (z : E.Choices) :
    OnlineWorkspace.Core script pub ((withTrace initial t).part z) small :=
  initial.source.append (core z)

theorem combinedCost (core : ∀ z, OnlineWorkspace.Core script pub (t.cut.part z) small) (z : E.Choices) :
    RAMBuckets.cost Report.probes (combinedCore initial t core z).logs =
      RAMBuckets.cost Report.probes initial.source.logs + RAMBuckets.cost Report.probes (core z).logs :=
  OnlineWorkspace.Core.cost_append ..

end CompressorRecords.ScheduledTrace.QuietInterval

end

end VPVNP
end Computability
end OAI
