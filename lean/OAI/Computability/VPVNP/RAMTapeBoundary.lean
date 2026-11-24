import OAI.Computability.VPVNP.RAMTapeBoundaryRecord
import OAI.Computability.VPVNP.RAMTapeBoundaryEnds
import OAI.Computability.VPVNP.RAMTapeBoundaryDecision
import Mathlib.Tactic.Linarith

/-!
# Finite stack execution of the local predecessor and last-record checks

The sorted input is a contiguous sequence of five-word slots. Each interior
endpoint contributes its raw five-word last-record field. The machine tests
a clamped field for zero on missing edges. Width and slot count come from
unary stacks. Every field loop takes the same number of instructions on
arbitrary data, including after a failure has been latched.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Boundary

open RAMBoundary

variable {w : ℕ}

private abbrev tally (n : ℕ) := List.replicate n true

private theorem scanRows (hp hs : Bool) (previous sent : RawSlot w) (xs : List (RawSlot w)) (ok : Bool) :
    let result := rows previous xs ok
    StackRuns (code hp hs) (xs.length * (45*w+17)) (.next ok)
      (store (blockBytes xs) (recordBytes previous) (recordBytes sent) (tally w) [] [] (tally xs.length))
      (.next result.2) (store [] (recordBytes result.1) (recordBytes sent) (tally w) [] [] []) := by
  induction xs generalizing previous ok with
  | nil =>
    simp only [rows, List.length_nil, Nat.zero_mul]
    exact .nil ..
  | cons current xs ih =>
    let n := tally xs.length
    let ok' := ok && checked (foldRecord previous current)
    have hr := record_run hp hs .row ok previous current [] (blockBytes xs) (recordBytes sent) [] n
    simp only [recordView, List.append_nil, ite_true] at hr
    have ht := restoreSlot_runs hp hs .row ok' (blockBytes xs) [] (recordBytes sent) (tally w) []
      (recordBytes current).reverse n
    simp only [ite_true, List.reverse_reverse, List.append_nil, List.length_reverse, length_recordBytes] at ht
    have hnext : StackRuns (code hp hs) 1 (.next ok)
        (store (blockBytes (current :: xs)) (recordBytes previous) (recordBytes sent)
          (tally w) [] [] (true :: n))
        (.field .row 0 ok (.tick initial))
        (store (recordBytes current ++ blockBytes xs) (recordBytes previous)
          (recordBytes sent) (tally w) [] [] n) := by
      refine .cons (.pop rfl) ?_
      simp only [store, update_store, List.head?_cons, List.tail_cons, Option.elim_some]
      exact .nil ..
    have h := ((hnext.trans hr).trans ht).trans (ih current ok')
    change StackRuns _ ((xs.length+1)*(45*w+17)) _ _ _ _
    rw [show (xs.length+1)*(45*w+17) =
      1 + 5*(7*w+3) + (2*(5*w)+1) + xs.length*(45*w+17) by rw [Nat.add_mul, Nat.one_mul]; omega]
    exact h

private theorem finish (hp hs : Bool) (last sent : RawSlot w) (ok : Bool) :
    StackRuns (code hp hs) (if hs then 45*w+17 else 5*w+2) (.next ok)
      (store [] (recordBytes last) (recordBytes sent) (tally w) [] [] [])
      (.done (ok && if hs then equalChecked (foldRecord last sent) else (recordBytes sent).all (!·)))
      (store [] (recordBytes (if hs then sent else last)) [] (tally w) [] [] []) := by
  cases hs with
  | false =>
    have h := checkSent_runs hp false ok [] (recordBytes last) (recordBytes sent) (tally w) [] [] []
    simp only [length_recordBytes] at h
    refine .cons (.pop rfl) ?_
    simpa only [store, update_store, List.head?_nil, List.tail_nil, Option.elim_none,
      Bool.false_eq_true, ite_false] using h
  | true =>
    let ok' := ok && equalChecked (foldRecord last sent)
    have hr := record_run hp true .edge ok last sent [] [] [] [] []
    simp only [recordView, List.append_nil, reduceCtorEq, ite_false] at hr
    have ht := restoreSlot_runs hp true .edge ok' [] [] [] (tally w) [] (recordBytes sent).reverse []
    simp only [reduceCtorEq, ite_false, List.reverse_reverse, List.append_nil, List.length_reverse,
      length_recordBytes] at ht
    have h := hr.trans ht
    simp only [ite_true]
    rw [show 45*w+17 = (5*(7*w+3)+(2*(5*w)+1))+1 by omega]
    refine .cons (.pop rfl) ?_
    simpa only [store, update_store, List.head?_nil, List.tail_nil, Option.elim_none, ite_true] using h

private theorem start (hp hs : Bool) (previous sent : RawSlot w) (block slots : List Bool) :
    let s := store block (recordBytes previous) (recordBytes sent) (tally w) [] [] slots
    StackRuns (code hp hs) (1 + if hp then 0 else 20*w+2) .start s
      (.next (hp || (recordBytes previous).all (!·))) s := by
  cases hp with
  | true => exact .cons (.goto rfl) (.nil ..)
  | false =>
    have h₁ := checkPrev_runs false hs true block (recordBytes previous) (recordBytes sent) (tally w) [] [] slots
    simp only [length_recordBytes, Bool.true_and, List.append_nil] at h₁
    have h₂ := restoreSlot_runs false hs .row ((recordBytes previous).all (!·)) block []
      (recordBytes sent) (tally w) [] (recordBytes previous).reverse slots
    simp only [ite_true, List.length_reverse, length_recordBytes, List.reverse_reverse, List.append_nil] at h₂
    have h := h₁.trans h₂
    simp only [Bool.false_eq_true, ite_false, Bool.false_or]
    rw [show 1+(20*w+2) = (2*(5*w)+1+(2*(5*w)+1))+1 by omega]
    exact .cons (.goto rfl) h

/-- Exact number of elementary stack steps, independent of the record bits. -/
def work (hasPredecessor hasSuccessor : Bool) (B w : ℕ) : ℕ :=
  (1 + if hasPredecessor then 0 else 20*w+2) + B*(45*w+17) + if hasSuccessor then 45*w+17 else 5*w+2

theorem work_le (hp hs : Bool) (B w : ℕ) : work hp hs B w ≤ 96*(B+1)*(w+1) := by
  cases hp <;> cases hs <;> simp only [work, ite_true, Bool.false_eq_true, ite_false] <;>
    nlinarith only [Nat.zero_le (B*w), Nat.zero_le B, Nat.zero_le w]

/-- The concrete finite control starts with just the two endpoint fields,
the sorted block, and two unary sizes. It implements all read, outgoing,
and clamping checks. It consumes the sorted block and both scratch stacks
finish empty. -/
theorem runs (hp hs : Bool) (previous sent : RawSlot w) (xs : List (RawSlot w)) :
    let result := rows previous xs (hp || (recordBytes previous).all (!·))
    StackRuns (code hp hs) (work hp hs xs.length w) .start
      (store (blockBytes xs) (recordBytes previous) (recordBytes sent) (List.replicate w true) [] []
        (List.replicate xs.length true))
      (.done (decision hp hs previous sent xs))
      (store [] (recordBytes (if hs then sent else result.1)) [] (List.replicate w true) [] [] []) := by
  let ok := hp || (recordBytes previous).all (!·)
  let result := rows previous xs ok
  exact ((start hp hs previous sent (blockBytes xs) (tally xs.length)).trans
    (scanRows hp hs previous sent xs ok)).trans (finish hp hs result.1 sent result.2)

/-- The deterministic pass contributes one accepting path exactly when
the scanned fields pass. The final instruction reads the latched status. -/
theorem path_count (hp hs : Bool) (previous sent : RawSlot w) (xs : List (RawSlot w)) :
    stackPaths (code hp hs) (1 + work hp hs xs.length w) .start
      (store (blockBytes xs) (recordBytes previous) (recordBytes sent) (List.replicate w true) [] []
        (List.replicate xs.length true)) =
      (decision hp hs previous sent xs).toNat := by
  rw [(runs hp hs previous sent xs).paths 1]
  rfl

/-- On a site's actual parsed edge fields the terminal stack program has
one accepting path precisely when the local `checkAt` predicate holds and
the two missing endpoint fields, when present in the physical layout, are zero. -/
theorem path_count_checkAt_iff {B S : ℕ} (hw : 2 ≤ w) (hB : 0 < B)
    (messages : RAMBoundary.Sends S (BurstRAM.Word w)) (v : Fin S)
    (previous sent : RawSlot w) (block : Fin B → RawSlot w)
    (hprev : (RAMSort.parsedSlot hw previous).record = RAMBoundary.receive messages v)
    (hsent : v.val+1 < S → (RAMSort.parsedSlot hw sent).record = RAMBoundary.outgoing messages v) :
    let hp := decide (0 < v.val)
    let hs := decide (v.val+1 < S)
    stackPaths (code hp hs) (1 + work hp hs B w) .start
      (store (blockBytes (List.ofFn block)) (recordBytes previous) (recordBytes sent)
        (List.replicate w true) [] [] (List.replicate B true)) = 1 ↔
      (v.val = 0 → (recordBytes previous).all (!·) = true) ∧
      RAMBoundary.checkAt hB messages v (fun i ↦ (RAMSort.parsedSlot hw (block i)).record) ∧
      (S ≤ v.val+1 → (recordBytes sent).all (!·) = true) := by
  let hp := decide (0 < v.val)
  let hs := decide (v.val+1 < S)
  have hc := path_count hp hs previous sent (List.ofFn block)
  simp only [List.length_ofFn] at hc
  have hedges : (if hs then some (RAMSort.parsedSlot hw sent).record else none) =
      (if v.val+1 < S then some (RAMBoundary.outgoing messages v) else none) := by
    by_cases he : v.val+1 < S <;> simp [hs, he, hsent]
  dsimp only
  rw [hc, Bool.toNat_eq_one, decision_scan hw, hprev, hedges]
  simp only [Bool.and_eq_true, Bool.or_eq_true, hp, hs, decide_eq_true_eq, RAMBoundary.scan_spec hB]
  grind

end RAMTape.Boundary

end VPVNP
end Computability
end OAI
