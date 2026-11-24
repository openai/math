import OAI.Computability.VPVNP.QueryScan

/-!
# Clocked simulation of a finite query program

For every query the head scans to the end of the input, then back to the selected payload
bit. The bound allows one final transition into a halting state, including on query timeout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace QueryMachine

open UniversalMachine TableCompiler QueryTape

variable {k : ℕ} {Q : Type*} [Fintype Q] (p : QueryProgram k Q) (t : ℕ)

private theorem readAtEnd (pre : Word) (x : Fin k → Bool) (r : Fin (t + 1)) (q : Q)
    {i : Fin k} {low high : Q} (hr : r.val ≠ 0) (hq : p.step q = .read i low high)
    (budget : ℕ) :
    countAt p t (pre ++ List.ofFn x) (pre.length + k) (r, q, 0) (k - i.val + 1 + budget) =
      countAt p t (pre ++ List.ofFn x) (pre.length + i.val)
        (predFin r, if x i then high else low, 0) budget := by
  let input := pre ++ List.ofFn x
  let base := pre.length + i.val
  let rem := k - i.val - 1
  have hphase : rem + 1 < k + 1 := by dsimp [rem]; omega
  let one : Fin (k + 1) := ⟨1, by omega⟩
  have hlast : input.length = pre.length + k := by simp [input]
  have hblank : (atPosition input (pre.length + k)).head = 0 := hlast ▸ head_atPosition_length input
  have hpos : pre.length + k = (base + rem) + 1 := by dsimp [base, rem]; omega
  have hoff : offset i = ⟨rem + 1, hphase⟩ := by apply Fin.ext; dsimp [offset, rem]; omega
  have depart (j : ℕ) :
      countAt p t input (pre.length + k) (r, q, 0) (j + 1) =
        countAt p t input (base + rem) (r, q, ⟨rem + 1, hphase⟩) j := by
    rw [countAt_step, hblank]
    simp [command, hq, hr, hoff, moveTape, hpos, move_left_atPosition_succ, countAt]
  have read : countAt p t input base (r, q, one) (budget + 1) =
      countAt p t input base (predFin r, if x i then high else low, 0) budget := by
    rw [countAt_step, show (atPosition input base).head = _ from head_atPosition_suffix pre x i]
    cases x i <;> simp [command, hq, hr, one, countAt, moveTape]
  have htime : k - i.val + 1 + budget = (rem + (budget + 1)) + 1 := by dsimp [rem]; omega
  rw [htime]
  exact (depart _).trans ((scanLeft p t input hr hq base rem (budget + 1) hphase).trans read)

private theorem runAt (pre : Word) (x : Fin k → Bool) (d : ℕ) (r : Fin (t + 1))
    (hrd : r.val = d) (q : Q) (pos ticks : ℕ) (hpos : pos ≤ pre.length + k)
    (ht : d * (pre.length + k + k + 1) + 1 ≤ ticks) :
    countAt p t (pre ++ List.ofFn x) pos (r, q, 0) ticks = (p.eval x d q).toNat := by
  induction d generalizing r q pos ticks with
  | zero =>
    obtain ⟨ticks, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
    rw [countAt_step]
    cases hq : p.step q with
    | halt b => cases b <;> simp [command, hq, QueryProgram.eval]
    | read i low high => simp [command, hq, hrd, QueryProgram.eval]
  | succ d ih =>
    cases hq : p.step q with
    | halt b =>
      obtain ⟨ticks, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
      rw [countAt_step]
      cases b <;> simp [command, hq, QueryProgram.eval]
    | read i low high =>
      let input := pre ++ List.ofFn x
      let dist := pre.length + k - pos
      let budget := ticks - (dist + (k - i.val + 1))
      have hr : r.val ≠ 0 := by omega
      have hlen : input.length = pre.length + k := by simp [input]
      have hend : pos + dist = input.length := by dsimp [dist]; omega
      rw [Nat.succ_mul] at ht
      have hbudget : d * (pre.length + k + k + 1) + 1 ≤ budget := by dsimp [budget, dist]; omega
      have htime : ticks = dist + (k - i.val + 1 + budget) := by dsimp [budget, dist]; omega
      have hpred : (predFin r).val = d := by dsimp [predFin]; omega
      simp only [QueryProgram.eval, hq]
      rw [htime, scanRight p t input hr hq pos dist _ hend, hlen, readAtEnd p t pre x r q hr hq]
      exact ih (predFin r) hpred _ (pre.length + i.val) budget (by omega) hbudget

/-- At every clock above the bound the literal table counts exactly the query result. -/
theorem correct (pre : Word) (x : Fin k → Bool) (ticks : ℕ)
    (ht : t * (pre.length + k + k + 1) + 1 ≤ ticks) :
    paths (machine p t) ticks (initial (machine p t) (pre ++ List.ofFn x)) =
      (p.eval x t p.start).toNat := by
  rw [machine, initial_eq_running]
  exact runAt p t pre x t (Fin.last t) rfl p.start 0 ticks (Nat.zero_le _) ht

end QueryMachine

end VPVNP
end Computability
end OAI
