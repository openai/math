import OAI.Computability.VPVNP.CompressorRecordsOrdinalFootprint

/-!
# Guarded deterministic compressor scans

The source call at ordinal `j` emits a concrete list of events and returns
`j+1`. Bounds on the read and write addresses of those events preserve the
scheduler's frame and control words throughout the scan. The resulting
trace can be replayed after the scheduler changes its own cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.StageFrame

open BurstRAM Schedule OrdinalRun SourceTransport
open scoped Fin.CommRing

variable {w d : ℕ} {Q : Type*}

/-- The exact returned cursor in each source report, including the terminal ordinal. -/
inductive Scanned : ℕ → ℕ → List (Report w) → Prop where
  | done (N : ℕ) : Scanned N N []
  | next {j N : ℕ} {r : Report w} {rs : List (Report w)} (live : j < N)
      (cursor : r.result = some ((j+1 : ℕ) : Word w)) (tail : Scanned (j+1) N rs) :
      Scanned j N (r :: rs)

/-- Establish ordinal order, terminal invariant and all accessed addresses before the
scheduler installs any worker frame. -/
theorem scan (P : BurstRAM.Program w Q) (fuel : ℕ) (first N : ℕ)
    (I : ℕ → Memory w → Prop) (events : Memory w → Word w → List (Event w))
    (readable writable : ℕ → Prop)
    (native : ∀ j, first ≤ j → j < N → ∀ m, execute P fuel (P.start (j : Word w)) m [] =
      some ⟨events m (j : Word w), some ((j : Word w)+1)⟩)
    (step : ∀ j, first ≤ j → j < N → ∀ m, I j m →
      I (j+1) (after m (events m (j : Word w))) ∧ Reads readable (events m (j : Word w)) ∧
        Writes writable (events m (j : Word w)))
    (first_le : first ≤ N) (m : Memory w) (rs : List (Report w)) (inv : I first m)
    (run : runSegment P fuel (some (first : Word w)) m (List.replicate (N-first) []) = some rs) :
    Scanned first N rs ∧ I N (after m (eventLog rs)) ∧
      Reads readable (eventLog rs) ∧ Writes writable (eventLog rs) := by
  have visit (count j : ℕ) (hj : first ≤ j) (size : j + count = N) (m : Memory w)
      (inv : I j m) (rs : List (Report w))
      (run : runSegment P fuel (some (j : Word w)) m (List.replicate count []) = some rs) :
      Scanned j N rs ∧ I N (after m (eventLog rs)) ∧
        Reads readable (eventLog rs) ∧ Writes writable (eventLog rs) := by
    induction count generalizing j m rs with
    | zero =>
      change some [] = some rs at run
      cases Option.some.inj run
      have h : j = N := by omega
      subst j
      exact ⟨.done _,inv,fun _ _ h ↦ (List.not_mem_nil h).elim,fun _ _ h ↦ (List.not_mem_nil h).elim⟩
    | succ count ih =>
      have hlt : j < N := by omega
      obtain ⟨next,rd,wr⟩ := step j hj hlt m inv
      rw [List.replicate_succ, runSegment, native j hj hlt m] at run
      simp only [← Nat.cast_add_one, Option.map_eq_some_iff] at run
      obtain ⟨tail, ht, rfl⟩ := run
      let rep : Report w := ⟨events m (j : Word w), some ((j+1 : ℕ) : Word w)⟩
      obtain ⟨vt,vi,vr,vw⟩ := ih (j+1) (by omega) (by omega) (after m rep.events) next tail ht
      refine ⟨.next hlt rfl vt, ?_, ?_, ?_⟩
      · change I N ((rep.events ++ eventLog tail).foldl update m)
        rwa [List.foldl_append]
      · intro a v ha
        exact (List.mem_append.mp ha).elim (rd a v) (vr a v)
      · intro a v ha
        exact (List.mem_append.mp ha).elim (wr a v) (vw a v)
  exact visit (N-first) first le_rfl (by omega) m inv rs run

/-- Ordinal order and write separation validate a guard in any prepared replay memory. -/
theorem Scanned.guarded (C : Catalog d) (worker : Fin d) (ports : Ports w)
    (pub : Fin (C worker).params → Word w) {first N : ℕ} {rs : List (Report w)}
    (shape : Scanned first N rs) (fit : N < 2^w) (writable : ℕ → Prop)
    (wr : Writes writable (eventLog rs)) (separate : ∀ x, ControlCell (C worker).params ports x → ¬ writable x)
    (m : Memory w) (ready : Ready C worker ports pub (N : Word w) m) :
    ValidTrace C worker ports pub (N : Word w) (first : Word w) m rs ∧
      Preserved (C worker).params ports m (after m (eventLog rs)) := by
  constructor
  · induction shape generalizing m with
    | done => exact ⟨ready,le_rfl⟩
    | @next j N r rs live cursor _ ih =>
      have hword : (j : Word w) < (N : Word w) := by
        change j%(2^w) < N%(2^w)
        rwa [Nat.mod_eq_of_lt (live.trans fit), Nat.mod_eq_of_lt fit]
      have keep : Preserved (C worker).params ports m (after m r.events) :=
        fun x hx ↦ after_outside m (fun a v ha ↦ wr a v (List.mem_append_left _ ha)) (separate x hx)
      exact ⟨ready,hword,_,cursor,ih fit (fun a v ha ↦ wr a v (List.mem_append_right _ ha)) _
        (ready_of_preserved C worker ports ready keep)⟩
  · exact fun x hx ↦ after_outside m wr (separate x hx)

/-- Prove guard validity and the footprint of the same genuine deterministic
source run. The source-specific invariant may track partial descriptor data. -/
theorem validScan (C : Catalog d) (worker : Fin d) (ports : Ports w) (P : BurstRAM.Program w Q)
    (fuel : ℕ) (pub : Fin (C worker).params → Word w) (first N : ℕ)
    (I : ℕ → Memory w → Prop) (events : Memory w → Word w → List (Event w))
    (readable writable : ℕ → Prop)
    (native : ∀ j, first ≤ j → j < N → ∀ m, execute P fuel (P.start (j : Word w)) m [] =
      some ⟨events m (j : Word w), some ((j : Word w)+1)⟩)
    (step : ∀ j, first ≤ j → j < N → ∀ m, I j m →
      I (j+1) (after m (events m (j : Word w))) ∧ Reads readable (events m (j : Word w)) ∧
        Writes writable (events m (j : Word w)))
    (separate : ∀ x, ControlCell (C worker).params ports x → ¬ writable x)
    (first_le : first ≤ N) (fit : N < 2^w)
    (m : Memory w) (rs : List (Report w)) (inv : I first m)
    (ready : Ready C worker ports pub (N : Word w) m)
    (run : runSegment P fuel (some (first : Word w)) m (List.replicate (N-first) []) = some rs) :
    ValidTrace C worker ports pub (N : Word w) (first : Word w) m rs ∧
      I N (after m (eventLog rs)) ∧ Reads readable (eventLog rs) ∧ Writes writable (eventLog rs) ∧
      Preserved (C worker).params ports m (after m (eventLog rs)) := by
  obtain ⟨shape,inv',rd,wr⟩ := scan P fuel first N I events readable writable native step first_le m rs inv run
  obtain ⟨valid,keep⟩ := shape.guarded C worker ports pub fit writable wr separate m ready
  exact ⟨valid,inv',rd,wr,keep⟩

end CompressorRecords.StageFrame

end VPVNP
end Computability
end OAI
