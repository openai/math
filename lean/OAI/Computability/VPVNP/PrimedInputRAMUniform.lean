import OAI.Computability.VPVNP.PrimedInputRAMRunEquiv

/-!
# A single burst-RAM program for both primed input passes

The first half of the public cursor range enumerates the designated scratch writes.
The second half enumerates all output writes, using the memory left by the first
half. The final halt contributes one extra unit to the calls-plus-probes bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

variable {N w : ℕ}

/-- Public data for the two passes, indexed by the rectangular tape positions. -/
structure TwoPass (N w : ℕ) where
  /-- Indicate which rectangular positions choose a shared bit in the first pass. -/
  own : Fin N → Bool
  /-- Distinct scratch address for each rectangular position, used for the first-pass choice
  writes. -/
  scratch : Fin N ↪ Word w
  /-- Distinct output address for each rectangular position assembled in the second pass. -/
  dest : Fin N ↪ Word w
  /-- Literal word or memory address supplying the second-pass copy at each position. -/
  source : Fin N → CopySource w

namespace TwoPass

variable (T : TwoPass N w)

/-- The cursor visits both full arrays in order. -/
def ops : Fin (N+N) → Item w :=
  Fin.append (fun i ↦ if T.own i then .choose (T.scratch i) else .skip)
    (fun i ↦ .copy (T.source i) (T.dest i))

@[simp] theorem owns_first (i : Fin N) : (T.ops (Fin.castAdd N i)).owns = T.own i := by
  cases h : T.own i <;> simp [ops, h, Item.owns]

theorem owns_second (i : Fin N) : (T.ops (Fin.natAdd N i)).owns = false := by
  rw [ops, Fin.append_right]
  rfl

@[simp] theorem owns_addNat (i : Fin N) : (T.ops (i.addNat N)).owns = false := by
  simpa only [Fin.natAdd_eq_addNat] using T.owns_second i

/-- Owners are exactly the original designated cells, at their first-pass cursors. -/
def assignmentEquiv : Assignment T.own ≃ Assignment (fun i ↦ (T.ops i).owns) where
  toFun f i := Fin.append (bitAt f) (fun _ ↦ false) i.val
  invFun g i := g ⟨Fin.castAdd N i.val, by simp [i.property]⟩
  left_inv f := by funext i; simp [bitAt, i.property]
  right_inv g := by
    funext ⟨i, hi⟩
    cases i using Fin.addCases with
    | left i => simp [bitAt, (T.owns_first i).symm.trans hi]
    | right i => exact Bool.noConfusion ((T.owns_second i).symm.trans hi)

@[simp] theorem bitAt_first (f : Assignment T.own) (i : Fin N) :
    bitAt (T.assignmentEquiv f) (Fin.castAdd N i) = bitAt f i := by
  cases h : T.own i <;> simp [assignmentEquiv, bitAt, h]

private theorem finRange_halves :
    List.finRange (N + N) =
      (List.finRange N).map (Fin.castAdd N) ++ (List.finRange N).map (Fin.natAdd N) := by
  change List.ofFn (id : Fin (N + N) → _) = _
  rw [List.ofFn_add]
  simp only [List.ofFn_eq_map, id_eq]
  rfl

private theorem first_reports_append (bitWord : Bool → Word w) (fit : N+N < 2^w)
    (g : Fin (N+N) → Bool) (cells : List (Fin N)) (tail : List (Fin (N+N))) (m : Memory w) :
    scheduledReports T.ops bitWord fit g (cells.map (Fin.castAdd N) ++ tail) m =
      reports T.own T.scratch (successor fit ∘ Fin.castAdd N) bitWord
        (g ∘ Fin.castAdd N) cells ++
      scheduledReports T.ops bitWord fit g tail
        (store T.scratch (bitWord ∘ g ∘ Fin.castAdd N) (cells.filter T.own) m) := by
  induction cells generalizing m with
  | nil => simp [reports, store]
  | cons i cells ih =>
    cases h : T.own i <;>
      simp [scheduledReports, reports, ops, h, Item.report, Item.memory, cellReport,
        store, Function.comp_def] at ih ⊢ <;> exact ih _

private theorem second_reports (bitWord : Bool → Word w) (fit : N+N < 2^w)
    (g : Fin (N+N) → Bool) (cells : List (Fin N)) (m : Memory w) :
    scheduledReports T.ops bitWord fit g (cells.map (Fin.natAdd N)) m =
      copyReports T.dest T.source (successor fit ∘ Fin.natAdd N) cells m := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih =>
    simp only [List.map_cons, scheduledReports, copyReports, ops, Fin.append_right, Item.report,
      Item.memory, Function.comp_apply]
    exact congrArg (_ :: ·) (ih _)

/-- Native data-call reports coincide with the first-pass and second-pass reports,
including all fetched values after the scratch writes. -/
theorem reports_split (bitWord : Bool → Word w) (fit : N+N < 2^w)
    (f : Assignment T.own) (m : Memory w) :
    scheduledReports T.ops bitWord fit (bitAt (T.assignmentEquiv f)) (List.finRange _) m =
      reports T.own T.scratch (successor fit ∘ Fin.castAdd N) bitWord (bitAt f) (List.finRange N) ++
      copyReports T.dest T.source (successor fit ∘ Fin.natAdd N) (List.finRange N)
        (store T.scratch (bitWord ∘ bitAt f) (owners T.own) m) := by
  rw [finRange_halves, first_reports_append, second_reports]
  simp only [Function.comp_def, bitAt_first, owners]

/-- Full report list, including the explicit halt after the copies. -/
def completeReports (bitWord : Bool → Word w) (fit : N+N < 2^w)
    (f : Assignment T.own) (m : Memory w) : List (Report w) :=
  scheduledReports T.ops bitWord fit (bitAt (T.assignmentEquiv f)) (List.finRange _) m ++ [haltReport w]

/-- Replaying the genuine RAM events produces the original two-pass memory. -/
theorem after_completeReports (bitWord : Bool → Word w) (fit : N+N < 2^w)
    (f : Assignment T.own) (m : Memory w) :
    after m (eventLog (T.completeReports bitWord fit f m)) =
      secondPass T.dest T.source (store T.scratch (bitWord ∘ bitAt f) (owners T.own) m) := by
  rw [completeReports, reports_split]
  simp only [eventLog, List.flatMap_append, List.flatMap_cons, haltReport, List.flatMap_nil,
    List.append_nil]
  rw [show ∀ xs ys : List (Event w), after m (xs ++ ys) = after (after m xs) ys by simp [after]]
  simp only [List.flatMap_def, after_reports, after_copyReports, secondPass, owners]

/-- One call and at most one write at each first-pass position, one call and at most
two probes per copy, and one final halt. -/
theorem completeReports_cost_le (bitWord : Bool → Word w) (fit : N+N < 2^w)
    (f : Assignment T.own) (m : Memory w) :
    RAMBuckets.cost Report.probes (T.completeReports bitWord fit f m) ≤ 5*N + 1 := by
  rw [completeReports, reports_split, RAMBuckets.cost_append, RAMBuckets.cost_append, reports_cost]
  have h := copyReports_cost_le T.dest T.source (successor fit ∘ Fin.natAdd N) (List.finRange N)
    (store T.scratch (bitWord ∘ bitAt f) (owners T.own) m)
  have hs := owners_length_le T.own
  rw [owners] at hs
  simp only [List.length_finRange, RAMBuckets.cost, haltReport, Report.probes, countProbes] at h ⊢
  omega

/-- Memory at the terminal cursor, before the explicit halt. This is the memory
available for a subsequent computation on the assembled tapes. -/
theorem scheduledMemory_eq (bitWord : Bool → Word w) (fit : N+N < 2^w)
    (f : Assignment T.own) (m : Memory w) :
    scheduledMemory T.ops bitWord (bitAt (T.assignmentEquiv f)) (List.finRange _) m =
      secondPass T.dest T.source (store T.scratch (bitWord ∘ bitAt f) (owners T.own) m) := by
  rw [← after_scheduledReports T.ops bitWord fit]
  simpa only [completeReports, eventLog, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, haltReport, List.append_nil] using T.after_completeReports bitWord fit f m

/-- Flattening the per-call histories recovers the original first-pass choice
stream in the order of the designated cells. -/
theorem flatten_assignmentCalls (f : Assignment T.own) :
    (assignmentCalls T.ops (T.assignmentEquiv f)).flatten = branches f := by
  have first (cells : List (Fin N)) :
      (cells.flatMap fun i ↦ (T.ops (Fin.castAdd N i)).bits
        (bitAt (T.assignmentEquiv f) (Fin.castAdd N i))) = (cells.filter T.own).map (bitAt f) := by
    induction cells with
    | nil => rfl
    | cons i cells ih =>
      rw [List.flatMap_cons, ih]
      cases h : T.own i <;> simp [Item.bits, h]
  have second (cells : List (Fin N)) :
      (cells.flatMap fun i ↦ (T.ops (Fin.natAdd N i)).bits
        (bitAt (T.assignmentEquiv f) (Fin.natAdd N i))) = [] := by
    induction cells with
    | nil => rfl
    | cons i cells ih =>
      rw [List.flatMap_cons, ih]
      simp only [Item.bits, owns_second, Bool.false_eq_true, ↓reduceIte, List.nil_append]
  rw [assignmentCalls, finRange_halves]
  simp only [List.map_append, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.map_map, ← List.flatMap_def, Function.comp_def, first, second, branches,
    owners]

/-- A completed two-pass run on a branch assignment computes exactly its reports. -/
theorem run_completeReports (bitWord : Bool → Word w) (fit : N+N < 2^w)
    (f : Assignment T.own) (m : Memory w) :
    runSegment (scheduledProgram T.ops bitWord fit) 3 (some 0) m
      (assignmentCalls T.ops (T.assignmentEquiv f)) = some (T.completeReports bitWord fit f m) :=
  run_generated T.ops bitWord fit (bitAt (T.assignmentEquiv f)) m

/-- The cap depends only on the number of cells, uniformly over bit assignments,
memory contents, and the number of fetches among the second-pass cells. -/
theorem scheduledCost_le (bitWord : Bool → Word w) (fit : N+N < 2^w) (m : Memory w) :
    scheduledCost T.ops ≤ 5*N + 1 := by
  let f : Assignment T.own := fun _ ↦ false
  rw [← generated_cost T.ops bitWord fit (bitAt (T.assignmentEquiv f)) m]
  exact T.completeReports_cost_le bitWord fit f m

theorem withinCaps_completeReports (bitWord : Bool → Word w) (fit : N+N < 2^w)
    (f : Assignment T.own) (m : Memory w) {S H : ℕ} (hH : 3 ≤ H) (hTotal : 5*N+1 ≤ S*H) :
    withinCaps S H (T.completeReports bitWord fit f m) :=
  scheduledReports_withinCaps T.ops bitWord fit (bitAt (T.assignmentEquiv f)) m hH
    ((T.scheduledCost_le bitWord fit m).trans hTotal)

/-- Bounded accepting paths of the single program enumerate precisely the original
designated-cell assignments, also when two branches encode the same memory word. -/
def actualPathEquiv (bitWord : Bool → Word w) (fit : N+N < 2^w) (m : Memory w)
    {S H : ℕ} (hH : 3 ≤ H) (hTotal : 5*N+1 ≤ S*H) :
    ActualPaths (scheduledProgram T.ops bitWord fit) 3 0 m (withinCaps S H) ≃ Assignment T.own :=
  (scheduledPathEquivWithinCaps T.ops bitWord fit m hH
    ((T.scheduledCost_le bitWord fit m).trans hTotal)).trans T.assignmentEquiv.symm

/-- For the assignment recovered from any accepted native path, the computed report
list is the canonical one with its observed choices and memory reads. -/
theorem run_actualPath (bitWord : Bool → Word w) (fit : N+N < 2^w) (m : Memory w)
    {S H : ℕ} (hH : 3 ≤ H) (hTotal : 5*N+1 ≤ S*H)
    (p : ActualPaths (scheduledProgram T.ops bitWord fit) 3 0 m (withinCaps S H)) :
    runSegment (scheduledProgram T.ops bitWord fit) 3 (some 0) m p.val =
      some (T.completeReports bitWord fit (T.actualPathEquiv bitWord fit m hH hTotal p) m) := by
  obtain ⟨f, rfl⟩ := (T.actualPathEquiv bitWord fit m hH hTotal).symm.surjective p
  rw [Equiv.apply_symm_apply]
  exact T.run_completeReports bitWord fit f m

end TwoPass
end PrimedInputRAM

end VPVNP
end Computability
end OAI
