import OAI.Computability.VPVNP.CompressorShrinkABSliceCalendar
import OAI.Computability.VPVNP.CompressorShrinkABSliceReads
import OAI.Computability.VPVNP.CompressorSourceObservableFrame

/-!
# Progress and footprints of the executed AB calendar

Each reset sequence advances the global bundle cursor and reads inside the
four input columns and the allocated bundle banks. These inputs suffice to
replay the full calendar. Applying the frame theorem to every compatible
initial memory shows that all emitted writes stay in the data region.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkABSliceRecipe

open BurstRAM SourceTransport ShrinkABSliceTable IndexedStarts

variable {w m n rows first : ℕ} {data : ℕ → Prop}
variable (I : Inputs) (pub : Fin 5 → Word w) (state : Word w) (ref : Memory w)
variable {t p : Fin 5 → Word w} (L : Layout t p rows m n first) (D : Describes I pub state ref t p rows first)

/-- The AB worker runs from cursor zero to the row count and all reads and writes in its report
log lie in the supplied data region. -/
def Guarded (rows cap : ℕ) (data : ℕ → Prop) (j : Stage m n) (mem : Memory w) (rs : List (Report w)) : Prop :=
  Source I pub state ref rows cap j mem rs ∧ SourceOnline.Progress (Fin.ofNat _ rows) 0 rs ∧
    Reads data (eventLog rs) ∧ Writes data (eventLog rs)

include L D

private theorem all_reads (R : ReadRegion t p rows m n first data) (limit : rows < 2^w) {cap : ℕ}
    (hcap : 95 ≤ cap) {js : List (Stage m n)} {mem : Memory w} {rs : List (Report w)}
    (walk : SourceWalk (Source I pub state ref rows cap) js mem rs) : Reads data (eventLog rs) := by
  induction walk with
  | done => simp [Reads,eventLog]
  | next head _ ih =>
    have one := (source_progress_reads I pub state ref L D R limit _ cap hcap _ _ head).2
    intro a v h
    rcases List.mem_append.mp (show Event.read a v ∈ _ ++ _ from by simpa only [eventLog,List.flatMap_append] using h) with h|h
    · exact one a v h
    · exact ih a v h

private theorem guarded_of_writes (R : ReadRegion t p rows m n first data) (limit : rows < 2^w) {cap : ℕ}
    (hcap : 95 ≤ cap) {js : List (Stage m n)} {mem : Memory w} {rs : List (Report w)}
    (walk : SourceWalk (Source I pub state ref rows cap) js mem rs) (wr : Writes data (eventLog rs)) :
    SourceWalk (Guarded (m := m) (n := n) I pub state ref rows cap data) js mem rs := by
  induction walk with
  | done => exact .done _
  | next head _ ih =>
    simp only [eventLog,List.flatMap_append] at wr
    have ⟨prog,rd⟩ := source_progress_reads I pub state ref L D R limit _ cap hcap _ _ head
    exact .next ⟨head,prog,rd,fun a v hv => wr a v (List.mem_append_left _ hv)⟩
      (ih (fun a v hv => wr a v (List.mem_append_right _ hv)))

/-- The same fixed stage list as the graph builder, with the scheduler's
per-packet progress, read and write predicates proved for its actual reports. -/
theorem guarded_walk [Nontrivial (Word w)] (R : ReadRegion t p rows m n first data) (limit : rows < 2^w)
    (old new : Fin rows → List ℕ) (om : ∀ i, (old i).length = m) (nm : ∀ i, (new i).length = n)
    (hs : ∀ i, (old i).sum < 2^w) (ht : ∀ i, (new i).sum < 2^w) (start : Memory w)
    (reads : ∀ i : Fin rows, SliceSchedule.Inputs (IndexedStarts.pair (columns t p i.val) (bank first m n i.val) m n)
      (old i) (new i) start)
    (cap : ℕ) (hcap : 95 ≤ cap) {rs : List (Report w)}
    (walk : SourceWalk (Source I pub state ref rows cap) (phases m n) start rs) :
    SourceWalk (Guarded I pub state ref rows cap data) (phases m n) start rs := by
  apply guarded_of_writes I pub state ref L D R limit hcap walk
  apply writes_of_replay
  intro mem agree x hx
  have read := all_reads I pub state ref L D R limit hcap walk
  have replay : SourceWalk (Source I pub state ref rows cap) (phases m n) mem rs :=
    replay_walk (src := Source I pub state ref rows cap) (fun _ _ _ _ ag rd h => (segment h ag rd).1) walk agree read
  have cells (i : Fin rows) (c : Fin 4) (j : ℕ) (hj : j < (if c.val < 2 then m else n)) :
      start (((columns t p i.val) c).val+j) = mem (((columns t p i.val) c).val+j) :=
    agree _ (R.columns i c j hj)
  have inputs (i : Fin rows) : SliceSchedule.Inputs
      (IndexedStarts.pair (columns t p i.val) (bank first m n i.val) m n) (old i) (new i) mem := by
    constructor <;> intro j hj
    · exact (cells i 0 j (om i ▸ hj)) ▸ (reads i).oldStart j hj
    · exact (cells i 1 j (om i ▸ hj)) ▸ (reads i).oldWidth j hj
    · exact (cells i 2 j (nm i ▸ hj)) ▸ (reads i).newStart j hj
    · exact (cells i 3 j (nm i ▸ hj)) ▸ (reads i).newWidth j hj
  obtain ⟨other,hw,_,out⟩ := run I pub state ref L D old new om nm hs ht mem inputs cap hcap
  have unique : other = rs := walk_deterministic (fun _ _ _ _ a b => Option.some.inj (a.symm.trans b)) hw replay
  subst other
  exact out x (by by_contra h; exact hx (R.bank x (by omega) (by omega)))

end CompressorRecords.ShrinkABSliceRecipe

end VPVNP
end Computability
end OAI
