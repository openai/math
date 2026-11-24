import OAI.Computability.VPVNP.RAMChain

/-!
# Transporting native source runs across scheduler writes

The online calendar changes its control cells between calls. If the
original reports read only data cells, the same worker produces exactly
the same reports in any memory agreeing on those cells. Every prefix of
the run preserves the data agreement. A separate write condition preserves
the scheduler's control cells throughout the source scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceTransport

open BurstRAM
variable {w : ℕ}

/-- The two memories return the same word at every address satisfying the data predicate. -/
def Agree (data : ℕ → Prop) (m m' : Memory w) : Prop := ∀ i, data i → m i = m' i

/-- Every read recorded in the event list addresses a cell satisfying the data predicate. -/
def Reads (data : ℕ → Prop) (es : List (Event w)) : Prop :=
  ∀ a v, Event.read a v ∈ es → data a.val

/-- Every write recorded in the event list addresses a cell satisfying the data predicate. -/
def Writes (data : ℕ → Prop) (es : List (Event w)) : Prop :=
  ∀ a v, Event.write a v ∈ es → data a.val

theorem Agree.update {data : ℕ → Prop} {m m' : Memory w} (h : Agree data m m') (e : Event w) :
    Agree data (update m e) (update m' e) := by
  intro i hi
  cases e <;> simp only [BurstRAM.update,writeMemory]
  all_goals first | exact h i hi | split <;> first | rfl | exact h i hi

theorem Agree.after {data : ℕ → Prop} {m m' : Memory w} (h : Agree data m m') (es : List (Event w)) :
    Agree data (after m es) (after m' es) := by
  induction es generalizing m m' with
  | nil => exact h
  | cons e es ih => exact ih (h.update e)

theorem Reads.tail {data : ℕ → Prop} {e : Event w} {es : List (Event w)} (h : Reads data (e::es)) :
    Reads data es := fun a v hv ↦ h a v (List.mem_cons_of_mem e hv)

theorem Writes.tail {data : ℕ → Prop} {e : Event w} {es : List (Event w)} (h : Writes data (e::es)) :
    Writes data es := fun a v hv ↦ h a v (List.mem_cons_of_mem e hv)

theorem correct {data : ℕ → Prop} {m m' : Memory w} {es : List (Event w)}
    (agree : Agree data m m') (reads : Reads data es) (ok : Correct m es) : Correct m' es := by
  induction es generalizing m m' with
  | nil => trivial
  | cons e es ih =>
    have tail := reads.tail
    cases e with
    | read a v => exact ⟨ok.1.trans (agree _ (reads a v (List.mem_cons_self))), ih agree tail ok.2⟩
    | tick => exact ih (agree.update .tick) tail ok
    | choice b => exact ih (agree.update (.choice b)) tail ok
    | write a v => exact ih (agree.update (.write a v)) tail ok

/-- The sequence of native calls is identical under any changes to addresses
outside its read region. Private state resets and branch choices are included. -/
theorem segment {C : Type*} {P : Program w C} {fuel s m m' bs rs} {data : ℕ → Prop}
    (run : runSegment P fuel s m bs = some rs) (agree : Agree data m m') (reads : Reads data (eventLog rs)) :
    runSegment P fuel s m' bs = some rs ∧ Agree data (after m (eventLog rs)) (after m' (eventLog rs)) := by
  obtain ⟨calls,ok,choices⟩ := (runSegment_iff ..).mp run
  exact ⟨(runSegment_iff ..).mpr ⟨calls,correct agree reads ok,choices⟩,agree.after _⟩

/-- No call in the native segment changes a cell outside the permitted writes. -/
theorem after_outside {data : ℕ → Prop} (m : Memory w) {es : List (Event w)}
    (writes : Writes data es) {i : ℕ} (hi : ¬ data i) : after m es i = m i := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih =>
    change after (update m e) es i = m i
    rw [ih _ writes.tail]
    cases e with
    | tick | choice | read => rfl
    | write a v =>
      have hne : i ≠ a.val := fun h ↦ hi (h ▸ writes a v List.mem_cons_self)
      exact ite_eq_right hne

/-- Inserting a prefix of online control writes leaves the original source
run executable and all of its data cells identical in the resulting memory. -/
theorem after_control {C : Type*} {P : Program w C} {fuel s m bs rs} (control : List (Event w))
    {data : ℕ → Prop} (run : runSegment P fuel s m bs = some rs)
    (outside : Writes (fun i ↦ ¬ data i) control) (reads : Reads data (eventLog rs)) :
    runSegment P fuel s (after m control) bs = some rs ∧
      Agree data (after m (eventLog rs)) (after (after m control) (eventLog rs)) :=
  segment run (fun _ hi ↦ (after_outside m outside (not_not_intro hi)).symm) reads

end CompressorRecords.SourceTransport

end VPVNP
end Computability
end OAI
