import OAI.Computability.VPVNP.CompressorSourceSequence
import OAI.Computability.VPVNP.CompressorScriptWindow

/-!
# Joining contiguous groups of online descriptor packets

Each group retains the actual execution on the raw memory, the event footprint and
clock bounds, and the recipe evaluation at the packet's live ordinal. Groups are
joined at the exact post-memory of their predecessors, shifting the ordinal by the
number of preceding visits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceOnline

open BurstRAM BlockPlanner DescriptorSpace

variable {w : ℕ}

/-- One online script visit together with its source memory and native worker reports. -/
abbrev Packet (A : Script) (w : ℕ) := SourceWalk.Packet (Visit A w) w

/-- Memory after replaying the reports from a list of online visit packets in order. -/
def post {A : Script} (m : Memory w) (ps : List (Packet A w)) := after m (eventLog (ps.flatMap SourceWalk.Packet.reports))

/-- Chronological packets whose runs satisfy the clock and memory bounds and whose recipes
match successive live ordinals. -/
structure Group (A : Script) (L : Layout) (base : Word w) (cap ordinal total : ℕ)
    (raw : Memory w) (ps : List (Packet A w)) : Prop where
  chronological : SourceWalk.Chronological Visit.Runs raw ps
  checked : ∀ p ∈ ps, Checked A L cap p
  prepared : ∀ i : Fin ps.length, Prepared A L base (ordinal+i.val) total ps[i.val]

private theorem chronological_append {A : Script} {ps qs : List (Packet A w)} {m : Memory w}
    (hp : SourceWalk.Chronological Visit.Runs m ps)
    (hq : SourceWalk.Chronological Visit.Runs (post m ps) qs) :
    SourceWalk.Chronological Visit.Runs m (ps++qs) := by
  induction ps generalizing m with
  | nil => exact hq
  | cons p ps ih =>
    refine ⟨hp.1,hp.2.1,ih hp.2.2 ?_⟩
    have he : post m (p::ps) = post p.output ps := by
      rw [← hp.1]
      simp only [post,List.flatMap_cons,SourceWalk.Packet.output,SourceWalk.after_append]
    rwa [← he]

theorem post_append {A : Script} (m : Memory w) (ps qs : List (Packet A w)) :
    post m (ps++qs) = post (post m ps) qs := by
  simp only [post,List.flatMap_append,SourceWalk.after_append]

namespace Group

variable {A : Script} {L : Layout} {base : Word w} {cap ordinal total : ℕ}
variable {m : Memory w} {ps qs : List (Packet A w)}

theorem nil : Group A L base cap ordinal total m [] :=
  ⟨trivial,by simp,fun i => Fin.elim0 i⟩

theorem singleton (p : Packet A w) (hin : p.input=m) (run : p.stage.Runs p.input p.reports)
    (checked : Checked A L cap p) (prepared : Prepared A L base ordinal total p) :
    Group A L base cap ordinal total m [p] := by
  refine ⟨⟨hin,run,trivial⟩,by simpa using checked,?_⟩
  intro i
  fin_cases i
  simpa using prepared

theorem append (first : Group A L base cap ordinal total m ps)
    (second : Group A L base cap (ordinal+ps.length) total (post m ps) qs) :
    Group A L base cap ordinal total m (ps++qs) := by
  refine ⟨chronological_append first.chronological second.chronological,?_,?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact first.checked p h
    · exact second.checked p h
  · intro i
    by_cases hi : i.val < ps.length
    · rw [List.getElem_append_left hi]
      exact first.prepared ⟨i.val,hi⟩
    · have hj : i.val-ps.length < qs.length := by have := i.isLt; simp only [List.length_append] at this; omega
      have hordinal : ordinal+i.val = (ordinal+ps.length)+(i.val-ps.length) := by omega
      rw [List.getElem_append_right (by omega),hordinal]
      exact second.prepared ⟨_,hj⟩

end Group
end CompressorRecords.SourceOnline

end VPVNP
end Computability
end OAI
