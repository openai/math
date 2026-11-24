import OAI.Computability.VPVNP.RAMTapeSpaceSeek
import OAI.Computability.VPVNP.RAMTapeStackAccess

/-!
# Displacement for a packed stack instruction

The seek and rewind cancel on each tape. The scratch head therefore returns
to its original position. At the next instruction boundary the first head
has moved left by one cell on a push, right by one on a successful pop, and
zero cells on an empty pop or a jump.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.StackCompiler

open UniversalMachine

variable {k : ℕ} {Q : Type*} (code : StackCode (Fin k) Q)

private theorem reachTravel (q : Q) (s : Stacks (Fin k)) (i : Fin k)
    (h : ∀ a b, rows code (.ready q) a b = .one (.next (.seek q i.castSucc) a 0 b 0)) :
    Travel (rows code) (3 * (fields (before s i)).length + 1)
      (fields (before s i)).length (-2 * (fields (before s i)).length)
      (.ready q) (tapeList (packed s)) (tapeList []) (.seek q 0)
      (tapeList ((s i).map bit ++ 0 :: fields (later s i)))
      (tapeList (scratch (fields (before s i)).reverse)) := by
  have first := Travel.single (t := tapeList (packed s)) (u := tapeList []) (h _ _)
  simp only [delta_stay, update_stay] at first
  have seek := seek_travel code q (before s i) (by simp [length_before])
    ((s i).map bit ++ 0 :: fields (later s i)) []
  have hi : (⟨(before s i).length, by rw [length_before]; omega⟩ : Fin (k+1)) = i.castSucc :=
    Fin.ext (length_before s i)
  rw [hi, ← List.append_assoc, ← packed_split] at seek
  simpa [scratch, Nat.add_comm] using first.trans seek

private theorem pushTravel {q q' : Q} {i : Fin k} {b : Bool} (h : code q = .push i b q')
    (s : Stacks (Fin k)) :
    Travel (rows code) (6 * (fields (before s i)).length + 4) (-1) 0
      (.ready q) (tapeList (packed s)) (tapeList [])
      (.ready q') (tapeList (packed (Function.update s i (b :: s i)))) (tapeList []) := by
  let pre := fields (before s i)
  let data := (s i).map bit ++ 0 :: fields (later s i)
  have reach := reachTravel code q s i (by simp [rows, h])
  have push : Travel (rows code) 2 (-1) 0 (.seek q 0) (tapeList data) (tapeList (scratch pre.reverse))
      (.restore q') (tapeList (bit b :: data)) (tapeList (scratch pre.reverse)) := by
    apply Travel.cons (dx := 0) (dy := 0) (show rows code (.seek q 0) _ _ =
      .one (.next (.pushing q' b) (tapeList data).head 1 (tapeList (scratch pre.reverse)).head 0)
      by simp [rows, h])
    simp only [left_for_push, update_stay]
    apply Travel.cons (d := 0) (e := 0) (dx := 0) (dy := 0) rfl
    simp only [replace_top, update_stay]
    exact .nil ..
  have run := (reach.trans push).trans (restore_travel code q' pre.reverse (bit b :: data))
  simp only [List.length_reverse, List.reverse_reverse] at run
  rw [packed_set, List.append_assoc, List.map_cons, List.cons_append]
  convert run using 1 <;> dsimp [pre] <;> omega

private theorem popTravel {q : Q} {i : Fin k} {f : Option Bool → Q} (h : code q = .pop i f)
    (s : Stacks (Fin k)) :
    Travel (rows code) (6 * (fields (before s i)).length + 3)
      ((s i).length - ((s i).tail.length : ℤ)) 0
      (.ready q) (tapeList (packed s)) (tapeList [])
      (.ready (f (s i).head?)) (tapeList (packed (Function.update s i (s i).tail))) (tapeList []) := by
  let pre := fields (before s i)
  let suffix := 0 :: fields (later s i)
  have reach := reachTravel code q s i (by simp [rows, h])
  have pop : Travel (rows code) 1 ((s i).length - ((s i).tail.length : ℤ)) 0
      (.seek q 0) (tapeList ((s i).map bit ++ suffix)) (tapeList (scratch pre.reverse))
      (.restore (f (s i).head?)) (tapeList ((s i).tail.map bit ++ suffix)) (tapeList (scratch pre.reverse)) := by
    cases hh : s i with
    | nil =>
      have step := Travel.single (code := rows code) (q := .seek q 0) (t := tapeList suffix)
        (u := tapeList (scratch pre.reverse))
        (show rows code (.seek q 0) _ _ = .one (.next (.restore (f none)) (tapeList suffix).head 0
          (tapeList (scratch pre.reverse)).head 0) by simp [rows, h, suffix])
      simpa using step
    | cons b bs =>
      have step := Travel.single (code := rows code) (q := .seek q 0)
        (t := tapeList (bit b :: (bs.map bit ++ suffix))) (u := tapeList (scratch pre.reverse))
        (show rows code (.seek q 0) _ _ = .one (.next (.restore (f (some b))) 0 2
          (tapeList (scratch pre.reverse)).head 0) by cases b <;> simp [rows, h, bit])
      simpa using step
  have run := (reach.trans pop).trans (restore_travel code (f (s i).head?) pre.reverse ((s i).tail.map bit ++ suffix))
  simp only [List.length_reverse, List.reverse_reverse] at run
  rw [packed_set, List.append_assoc]
  convert run using 1 <;> dsimp [pre] <;> omega

/-- A deterministic stack instruction costs a positive number of transitions.
At the next instruction boundary, growth of the packed bank gives the exact
negative displacement of its head. -/
theorem step_travel {s s' : Stacks (Fin k)} {q q' : Q} (h : StackStep code q s q' s') :
    ∃ ticks, 0 < ticks ∧ ticks ≤ 6 * (packed s).length + 4 ∧
      Travel (rows code) ticks ((packed s).length - ((packed s').length : ℤ)) 0
        (.ready q) (tapeList (packed s)) (tapeList []) (.ready q') (tapeList (packed s')) (tapeList []) := by
  have bound (i : Fin k) : (fields (before s i)).length ≤ (packed s).length := by
    rw [packed_split s i]
    simp
  cases h with
  | push h =>
    rename_i i b
    have hb := bound i
    refine ⟨6 * (fields (before s i)).length + 4, by omega, ?_, ?_⟩
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left 6 hb) 4
    · convert pushTravel code h s using 1
      rw [packed_set, packed_split s i]
      simp
  | pop h =>
    rename_i i f
    have hb := bound i
    refine ⟨6 * (fields (before s i)).length + 3, by omega, by omega, ?_⟩
    convert popTravel code h s using 1
    rw [packed_set, packed_split s i]
    simp
  | goto h =>
    refine ⟨1, by decide, by omega, ?_⟩
    have step := Travel.single (code := rows code) (q := .ready q) (t := tapeList (packed s)) (u := tapeList [])
      (show rows code (.ready q) _ _ = .one (.next (.ready q') (tapeList (packed s)).head 0 (tapeList []).head 0)
        by simp [rows, h])
    simpa only [delta_stay, update_stay, sub_self] using step

end RAMTape.StackCompiler

end VPVNP
end Computability
end OAI
