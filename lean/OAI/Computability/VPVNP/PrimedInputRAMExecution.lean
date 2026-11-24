import OAI.Computability.VPVNP.PrimedInputRAMSchedule

/-!
# Complete native execution of the cursor-controlled input program

Every accepting native path performs the entire public schedule followed by one
halt call. Its only private branch bits are those at the scheduled choice positions.
Conversely, every such assignment determines all reads, writes and reports uniquely.
The prefix theorem allows replacing the terminal call with the grammar parser.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

variable {M w : ℕ}

/-- Final memory obtained by executing the indicated cursor items. -/
def scheduledMemory (ops : Fin M → Item w) (bitWord : Bool → Word w) (f : Fin M → Bool) :
    List (Fin M) → Memory w → Memory w
  | [], m => m
  | i :: xs, m => scheduledMemory ops bitWord f xs ((ops i).memory bitWord m (f i))

theorem after_scheduledReports (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w)
    (f : Fin M → Bool) (xs : List (Fin M)) (m : Memory w) :
    after m (eventLog (scheduledReports ops bitWord fit f xs m)) = scheduledMemory ops bitWord f xs m := by
  induction xs generalizing m with
  | nil => rfl
  | cons i xs ih =>
    simp only [scheduledReports, eventLog, List.flatMap_cons, scheduledMemory]
    rw [show ∀ es tail, after m (es ++ tail) = after (after m es) tail by simp [after]]
    rw [Item.after_report]
    exact ih _

/-- The remaining cells form the consecutive suffix beginning at cursor k and ending at the
exclusive schedule bound. -/
def Aligned (k : ℕ) (cells : List (Fin M)) : Prop :=
  cells.map Fin.val = List.range' k cells.length ∧ k + cells.length = M

theorem aligned_all (M : ℕ) : Aligned 0 (List.finRange M) := by
  constructor
  · apply List.ext_getElem (by simp)
    intro i _ _
    simp
  · simp

theorem aligned_cons {k : ℕ} {i : Fin M} {xs : List (Fin M)} (ha : Aligned k (i::xs)) :
    i.val = k ∧ Aligned (k+1) xs := by
  obtain ⟨he, hl⟩ := ha
  simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at he
  exact ⟨he.1, he.2, by simp only [List.length_cons] at hl; omega⟩

theorem aligned_fresh {k : ℕ} {i : Fin M} {xs : List (Fin M)} (ha : Aligned k (i::xs)) :
    i ∉ xs := by
  obtain ⟨hi, ht, _⟩ := aligned_cons ha
  intro hm
  have hval : i.val ∈ xs.map Fin.val := List.mem_map_of_mem hm
  rw [ht, List.mem_range'_1, hi] at hval
  omega

private theorem run_prefix_aux {C : Type*} (P : Program w C) (fuel : ℕ) (ops : Fin M → Item w)
    (bitWord : Bool → Word w) (fit : M < 2^w)
    (hstep : ∀ (i : Fin M) (m : Memory w) (b : Bool),
      execute P fuel (P.start (cursor fit i.val i.isLt.le)) m ((ops i).bits b) =
        some ((ops i).report bitWord (successor fit i) m b)) (f : Fin M → Bool) (cells : List (Fin M)) (k : ℕ) (hk : k ≤ M) (ha : Aligned k cells)
    (m : Memory w) (tail : List (List Bool)) :
    runSegment P fuel (some (cursor fit k hk)) m
      (cells.map (fun i ↦ (ops i).bits (f i)) ++ tail) =
      (runSegment P fuel (some (cursor fit M le_rfl))
        (scheduledMemory ops bitWord f cells m) tail).map
        (fun ts ↦ scheduledReports ops bitWord fit f cells m ++ ts) := by
  induction cells generalizing k m with
  | nil =>
    have he : k = M := by simpa using ha.2
    subst k
    simp [scheduledReports, scheduledMemory]
  | cons i xs ih =>
    obtain ⟨hi, ht⟩ := aligned_cons ha
    subst k
    simp only [List.map_cons, List.cons_append, runSegment, hstep,
      Item.after_report, Item.report_result, scheduledReports, scheduledMemory]
    rw [show successor fit i = cursor fit (i.val+1) i.isLt by rfl, ih _ _ ht]
    simp only [Option.map_map, Function.comp_def]

/-- Stitch this input stage to any following program with the same data calls. At cursor
`M` its continuation can start the grammar parser; the prefix fixes its memory and leaves
its private choice streams untouched. -/
theorem splice_scheduledPrefix {C : Type*} (P : Program w C) (fuel : ℕ) (ops : Fin M → Item w)
    (bitWord : Bool → Word w) (fit : M < 2^w)
    (hstep : ∀ (i : Fin M) (m : Memory w) (b : Bool),
      execute P fuel (P.start (cursor fit i.val i.isLt.le)) m ((ops i).bits b) =
        some ((ops i).report bitWord (successor fit i) m b))
    (f : Fin M → Bool) (m : Memory w) (tail : List (List Bool)) :
    runSegment P fuel (some 0) m ((List.finRange M).map (fun i ↦ (ops i).bits (f i)) ++ tail) =
      (runSegment P fuel (some (cursor fit M le_rfl)) (scheduledMemory ops bitWord f (List.finRange M) m)
        tail).map (fun ts ↦ scheduledReports ops bitWord fit f (List.finRange M) m ++ ts) :=
  run_prefix_aux P fuel ops bitWord fit hstep f _ 0 (Nat.zero_le _) (aligned_all M) m tail

/-- Execute the data calls and supply an arbitrary continuation from the terminal cursor. -/
theorem scheduled_prefix (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w)
    (f : Fin M → Bool) (m : Memory w) (tail : List (List Bool)) :
    runSegment (scheduledProgram ops bitWord fit) 3 (some 0) m
      ((List.finRange M).map (fun i ↦ (ops i).bits (f i)) ++ tail) =
      (runSegment (scheduledProgram ops bitWord fit) 3 (some (cursor fit M le_rfl))
        (scheduledMemory ops bitWord f (List.finRange M) m) tail).map
        (fun ts ↦ scheduledReports ops bitWord fit f (List.finRange M) m ++ ts) :=
  splice_scheduledPrefix _ _ _ _ _ (fun i mem b ↦ by
    rw [start_item]
    exact execute_item ops bitWord fit (ops i) (successor fit i) mem b) f m tail

/-- Every scheduled assignment yields its complete native report list. -/
theorem run_generated (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w)
    (f : Fin M → Bool) (m : Memory w) :
    runSegment (scheduledProgram ops bitWord fit) 3 (some 0) m
      ((List.finRange M).map (fun i ↦ (ops i).bits (f i)) ++ [[]]) =
      some (scheduledReports ops bitWord fit f (List.finRange M) m ++ [haltReport w]) := by
  rw [scheduled_prefix, runSegment, start_halt]
  rfl

theorem unpack_call {C : Type*} (P : Program w C) (fuel : ℕ) (s : Word w) (m : Memory w)
    (bs : List Bool) (more : List (List Bool)) (rs : List (Report w))
    (h : runSegment P fuel (some s) m (bs::more) = some rs) :
    ∃ r ts, execute P fuel (P.start s) m bs = some r ∧
      runSegment P fuel r.result (after m r.events) more = some ts ∧ rs = r::ts := by
  rw [runSegment] at h
  cases he : execute P fuel (P.start s) m bs with
  | none => simp [he] at h
  | some r =>
    simp only [he, Option.map_eq_some_iff] at h
    obtain ⟨ts, hr, heq⟩ := h
    exact ⟨r, ts, rfl, hr, heq.symm⟩

private theorem generated_of_run (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w)
    (cells : List (Fin M)) (k : ℕ) (hk : k ≤ M) (ha : Aligned k cells)
    (m : Memory w) (bits : List (List Bool)) (rs : List (Report w))
    (hr : runSegment (scheduledProgram ops bitWord fit) 3 (some (cursor fit k hk)) m bits = some rs)
    (hend : endState (some (cursor fit k hk)) rs = none) :
    ∃ f : Fin M → Bool, bits = cells.map (fun i ↦ (ops i).bits (f i)) ++ [[]] := by
  induction cells generalizing k m bits rs with
  | nil =>
    have he : k = M := by simpa using ha.2
    subst k
    cases bits with
    | nil => simp [runSegment] at hr; subst rs; contradiction
    | cons bs more =>
      obtain ⟨r, ts, he, ht, rfl⟩ := unpack_call _ 3 _ _ _ _ _ hr
      rw [start_halt] at he
      cases bs with
      | nil =>
        have heq : haltReport w = r := Option.some.inj he
        subst r
        cases more with
        | nil => exact ⟨fun _ ↦ false, rfl⟩
        | cons => contradiction
      | cons => contradiction
  | cons i xs ih =>
    obtain ⟨hi, ht⟩ := aligned_cons ha
    have fresh := aligned_fresh ha
    subst k
    cases bits with
    | nil => simp [runSegment] at hr; subst rs; contradiction
    | cons bs more =>
      obtain ⟨r, ts, he, hr', rfl⟩ := unpack_call _ 3 _ _ _ _ _ hr
      rw [start_item] at he
      obtain ⟨b, rfl, rfl⟩ := execute_item_only _ _ _ _ _ _ _ _ he
      simp only [Item.after_report, Item.report_result] at hr'
      simp only [endState, Item.report_result] at hend
      obtain ⟨f, rfl⟩ := ih _ i.isLt ht _ _ ts hr' hend
      refine ⟨fun j ↦ if j = i then b else f j, ?_⟩
      simp only [List.map_cons, List.cons_append, ↓reduceIte, List.cons.injEq, true_and]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hne : j ≠ i := fun h ↦ fresh (h ▸ hj)
      simp [hne]

/-- The native accepting paths consist of the scheduled owner choices, with empty
private streams for the remaining calls and the terminal halt. -/
theorem run_accepted_iff (ops : Fin M → Item w) (bitWord : Bool → Word w) (fit : M < 2^w)
    (m : Memory w) (bs : List (List Bool)) :
    (∃ rs, runSegment (scheduledProgram ops bitWord fit) 3 (some 0) m bs = some rs ∧
      endState (some 0) rs = none) ↔
    ∃ f : Fin M → Bool, bs = (List.finRange M).map (fun i ↦ (ops i).bits (f i)) ++ [[]] := by
  constructor
  · rintro ⟨rs, hr, hend⟩
    exact generated_of_run ops bitWord fit _ 0 (Nat.zero_le _) (aligned_all M) m bs rs hr hend
  · rintro ⟨f, rfl⟩
    exact ⟨_, run_generated ops bitWord fit f m, by rw [endState_append]; rfl⟩

end PrimedInputRAM

end VPVNP
end Computability
end OAI
