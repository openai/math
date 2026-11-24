import OAI.Computability.VPVNP.RAMTapeStackScan

/-!
# A literal stack operation at any address

The machine returns to the beginning of the packed stack bank with empty
scratch. The exact cost depends on the number of preceding cells, not on
the value stored in the addressed stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.StackCompiler

open UniversalMachine

variable {k : ℕ} {Q : Type*} (code : StackCode (Fin k) Q)

/-- The primary tape's complete representation of a finite stack bank. -/
def packed (s : Stacks (Fin k)) := fields (List.ofFn s)

/-- Stack fields before the selected ordinal in the packed bank. -/
def before (s : Stacks (Fin k)) (i : Fin k) := (List.ofFn s).take i.val
/-- Stack fields after the selected ordinal in the packed bank. -/
def later (s : Stacks (Fin k)) (i : Fin k) := (List.ofFn s).drop (i.val+1)

theorem length_before (s : Stacks (Fin k)) (i : Fin k) : (before s i).length = i.val := by
  simp [before]

private theorem fields_append (ss tt : List (List Bool)) :
    fields (ss ++ tt) = fields ss ++ fields tt := List.flatMap_append ..

private theorem ofFn_set (s : Stacks (Fin k)) (i : Fin k) (a : List Bool) :
    List.ofFn (Function.update s i a) = (List.ofFn s).set i.val a := by
  apply List.ext_getElem (by simp)
  intro j hj _
  rw [List.getElem_ofFn, List.getElem_set]
  by_cases he : i.val = j
  · subst j
    simp
  · simp [he, Function.update_of_ne (show (⟨j, by simpa using hj⟩ : Fin k) ≠ i by
      intro h; exact he (congrArg Fin.val h).symm)]

theorem packed_set (s : Stacks (Fin k)) (i : Fin k) (a : List Bool) :
    packed (Function.update s i a) = fields (before s i) ++ a.map bit ++ 0 :: fields (later s i) := by
  simp only [packed, ofFn_set, List.set_eq_take_append_cons_drop, List.length_ofFn,
    i.isLt, ↓reduceIte, fields_append, fields_cons, List.append_assoc, before, later]

theorem packed_split (s : Stacks (Fin k)) (i : Fin k) :
    packed s = fields (before s i) ++ (s i).map bit ++ 0 :: fields (later s i) := by
  simpa using packed_set s i (s i)

private theorem reach (q : Q) (s : Stacks (Fin k)) (i : Fin k)
    (h : ∀ a b, rows code (.ready q) a b = .one (.next (.seek q i.castSucc) a 0 b 0)) :
    Runs (rows code) (3 * (fields (before s i)).length + 1) (.ready q) (tapeList (packed s))
      (tapeList []) (.seek q 0) (tapeList ((s i).map bit ++ 0 :: fields (later s i)))
      (tapeList (scratch (fields (before s i)).reverse)) := by
  apply Runs.cons (h _ _)
  simp only [update_stay]
  rw [packed_split s i, List.append_assoc]
  have hp := seek_run code q (before s i) (by simp [length_before]) ((s i).map bit ++ 0 :: fields (later s i)) []
  have hi : (⟨(before s i).length, by rw [length_before]; omega⟩ : Fin (k+1)) = i.castSucc :=
    Fin.ext (length_before s i)
  rw [hi] at hp
  simpa [scratch] using hp

theorem push_run {q q' : Q} {i : Fin k} {b : Bool} (h : code q = .push i b q')
    (s : Stacks (Fin k)) :
    Runs (rows code) (6 * (fields (before s i)).length + 4) (.ready q) (tapeList (packed s)) (tapeList [])
      (.ready q') (tapeList (packed (Function.update s i (b :: s i)))) (tapeList []) := by
  let pre := fields (before s i)
  let data := (s i).map bit ++ 0 :: fields (later s i)
  have hr := reach code q s i (by simp [rows, h])
  have hp : Runs (rows code) 2 (.seek q 0) (tapeList data) (tapeList (scratch pre.reverse))
      (.restore q') (tapeList (bit b :: data)) (tapeList (scratch pre.reverse)) := by
    apply Runs.cons (show rows code (.seek q 0) _ _ = .one (.next (.pushing q' b) (tapeList data).head 1 (tapeList (scratch pre.reverse)).head 0)
      by simp [rows, h])
    simp only [left_for_push, update_stay]
    apply Runs.cons rfl
    simp only [replace_top, update_stay]
    exact .nil ..
  have hs := (hr.trans hp).trans (restore_run code q' pre.reverse (bit b :: data))
  simp only [List.length_reverse, List.reverse_reverse] at hs
  rw [packed_set, List.append_assoc, List.map_cons, List.cons_append]
  convert hs using 1
  dsimp [pre]
  omega

theorem pop_run {q : Q} {i : Fin k} {f : Option Bool → Q} (h : code q = .pop i f)
    (s : Stacks (Fin k)) :
    Runs (rows code) (6 * (fields (before s i)).length + 3) (.ready q) (tapeList (packed s)) (tapeList [])
      (.ready (f (s i).head?)) (tapeList (packed (Function.update s i (s i).tail))) (tapeList []) := by
  let pre := fields (before s i)
  let suffix := 0 :: fields (later s i)
  have hr := reach code q s i (by simp [rows, h])
  have hp : Runs (rows code) 1 (.seek q 0) (tapeList ((s i).map bit ++ suffix))
      (tapeList (scratch pre.reverse)) (.restore (f (s i).head?))
      (tapeList ((s i).tail.map bit ++ suffix)) (tapeList (scratch pre.reverse)) := by
    cases hh : s i with
    | nil =>
      have hs := Runs.single (code := rows code) (q := .seek q 0) (t := tapeList suffix)
        (u := tapeList (scratch pre.reverse))
        (show rows code (.seek q 0) _ _ = .one (.next (.restore (f none)) (tapeList suffix).head 0 (tapeList (scratch pre.reverse)).head 0) by simp [rows, h, suffix])
      simpa [update_stay] using hs
    | cons b bs =>
      have hs := Runs.single (code := rows code) (q := .seek q 0)
        (t := tapeList (bit b :: (bs.map bit ++ suffix))) (u := tapeList (scratch pre.reverse))
        (show rows code (.seek q 0) _ _ = .one (.next (.restore (f (some b))) 0 2 (tapeList (scratch pre.reverse)).head 0)
          by cases b <;> simp [rows, h, bit])
      simpa [pop_cell, update_stay] using hs
  have hs := (hr.trans hp).trans (restore_run code (f (s i).head?) pre.reverse ((s i).tail.map bit ++ suffix))
  simp only [List.length_reverse, List.reverse_reverse] at hs
  rw [packed_set, List.append_assoc]
  convert hs using 1
  dsimp [pre]
  omega

end RAMTape.StackCompiler

end VPVNP
end Computability
end OAI
