import OAI.Computability.VPVNP.RAMTapeStackAccess

/-!
# Path counts and clock of the physical stack interpreter

At most one packed cell is added by each stack instruction. Seeking and
restoring any stack costs at most six transitions per preceding cell, plus
four for dispatch and the operation itself. Every virtual choice is a
single literal two-record row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.StackCompiler

open UniversalMachine

variable {k : ℕ} {Q : Type*} (code : StackCode (Fin k) Q)

private theorem before_le (s : Stacks (Fin k)) (i : Fin k) :
    (fields (before s i)).length ≤ (packed s).length := by
  rw [packed_split s i]
  simp

theorem step_size {s s' : Stacks (Fin k)} {q q' : Q} (h : StackStep code q s q' s') :
    (packed s').length ≤ (packed s).length + 1 := by
  cases h with
  | goto => omega
  | push =>
    rename_i i b _
    rw [packed_set, packed_split s i]
    simp
    omega
  | pop =>
    rename_i i _ _
    rw [packed_set, packed_split s i]
    simp
    omega

theorem step_run {s s' : Stacks (Fin k)} {q q' : Q} (h : StackStep code q s q' s') :
    ∃ ticks ≤ 6*(packed s).length+4, Runs (rows code) ticks
      (.ready q) (tapeList (packed s)) (tapeList []) (.ready q') (tapeList (packed s')) (tapeList []) := by
  cases h with
  | push h =>
    exact ⟨_, Nat.add_le_add_right (Nat.mul_le_mul_left 6 (before_le ..)) _, push_run code h s⟩
  | pop h =>
    rename_i i f
    have hb := before_le s i
    exact ⟨_, by omega, pop_run code h s⟩
  | goto h =>
    refine ⟨1, by omega, ?_⟩
    apply Runs.cons (show rows code (.ready q) _ _ =
      .one (.next (.ready q') (tapeList (packed s)).head 0 (tapeList []).head 0) by simp [rows, h])
    simp only [update_stay]
    exact .nil ..

variable [Fintype Q]

/-- Accepting path count on the packed primary tape and initially empty scratch tape. -/
noncomputable abbrev physical (start : Q) (ticks : ℕ) (q : Q) (s : Stacks (Fin k)) :=
  count (.ready start) (rows code) ticks (.ready q) (tapeList (packed s)) (tapeList [])

private theorem count_step (start : Q) {t B ticks : ℕ} {q s q' s'}
    (h : StackStep code q s q' s') (hsize : (packed s).length+t+1 ≤ B)
    (hclock : (t+1)*(6*B+4) ≤ ticks)
    (ih : ∀ left, (packed s').length+t ≤ B → t*(6*B+4) ≤ left →
      physical code start left q' s' = stackPaths code t q' s') :
    physical code start ticks q s = stackPaths code t q' s' := by
  obtain ⟨d, hd, run⟩ := step_run code h
  have hg := step_size code h
  have hb : d ≤ 6*B+4 := by omega
  rw [Nat.succ_mul] at hclock
  have he : ticks - d + d = ticks := by omega
  have hr := run.count (.ready start) (ticks-d)
  rw [he] at hr
  exact hr.trans (ih _ (by omega) (by omega))

/-- All virtual leaves have been reached by the indicated physical clock.
This compares the actual integer path counts, with repeated targets counted
once per incoming branch slot. -/
theorem physical_eq (start : Q) (t : ℕ) (q : Q) (s : Stacks (Fin k)) (B ticks : ℕ)
    (stops : StopsWithin code t q s) (hsize : (packed s).length+t ≤ B)
    (hclock : t*(6*B+4) ≤ ticks) :
    physical code start ticks q s = stackPaths code t q s := by
  induction t generalizing q s ticks with
  | zero => exact stops.elim
  | succ t ih =>
    cases h : code q with
    | push i b r =>
      simp only [StopsWithin, h] at stops
      simp only [stackPaths, h]
      exact count_step code start (.push h) (by omega) hclock (fun _ => ih _ _ _ stops)
    | pop i f =>
      simp only [StopsWithin, h] at stops
      simp only [stackPaths, h]
      exact count_step code start (.pop h) (by omega) hclock (fun _ => ih _ _ _ stops)
    | goto r =>
      simp only [StopsWithin, h] at stops
      simp only [stackPaths, h]
      exact count_step code start (.goto h) (by omega) hclock (fun _ => ih _ _ _ stops)
    | choose low high =>
      simp only [StopsWithin, h] at stops
      rw [Nat.succ_mul] at hclock
      obtain ⟨ticks, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
      change count _ _ (ticks+1) _ _ _ = _
      rw [paths_step]
      simp only [rows, h, after, update_stay, stackPaths]
      exact congrArg₂ Nat.add (ih low s ticks stops.1 (by omega) (by omega))
        (ih high s ticks stops.2 (by omega) (by omega))
    | halt b =>
      rw [Nat.succ_mul] at hclock
      obtain ⟨ticks, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
      change count _ _ (ticks+1) _ _ _ = _
      rw [paths_step]
      simp only [rows, h, after, stackPaths]

end RAMTape.StackCompiler

end VPVNP
end Computability
end OAI
