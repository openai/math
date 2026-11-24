import OAI.Computability.VPVNP.IncidenceControl
import OAI.Computability.VPVNP.ProgramLength
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-! # Iterating the incidence matrix passes

Between two row checks the head scans to the blank at the right end of the
input. A final pass halts with acceptance precisely when every row check
succeeded. The running-time bound includes all scans across the padded prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace IncidenceMachine

open UniversalMachine TableCompiler QueryTape
open scoped Classical

theorem card_state (m : ℕ) : Fintype.card (State m) = (m + 1) + m * 3 + m * 3 + m * m * 6 := by
  let e : State m ≃ Fin (m+1) ⊕ (Fin m × Fin 3) ⊕ (Fin m × Fin 3) ⊕
      (Fin m × Fin m × Bool × Fin 3) :=
    { toFun := fun q => match q with
        | .search r => .inl r
        | .tag r z => .inr (.inl (r,z))
        | .flag r z => .inr (.inr (.inl (r,z)))
        | .bit r i s z => .inr (.inr (.inr (r,i,s,z)))
      invFun := fun q => match q with
        | .inl r => .search r
        | .inr (.inl (r,z)) => .tag r z
        | .inr (.inr (.inl (r,z))) => .flag r z
        | .inr (.inr (.inr (r,i,s,z))) => .bit r i s z
      left_inv := fun q => by cases q <;> rfl
      right_inv := fun q => by rcases q with _ | (_ | (_ | _)) <;> rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

theorem programLength_le (m : ℕ) :
    (programPrefix (machine m)).length ≤ 1000000 * (m+1)^4 := by
  have hp := programPrefix_length_le (machine m)
  have hc : (machine m).extra = Fintype.card (State m) := rfl
  rw [hc, card_state] at hp
  have hsmall : (m+1)+m*3+m*3+m*m*6+1 ≤ 20*(m+1)^2 := by
    nlinarith [Nat.zero_le (m*m)]
  calc
    _ ≤ 1000 * (20*(m+1)^2)^2 := hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmall 2))
    _ = 400000 * (m+1)^4 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

private theorem scanRight {m : ℕ} (input : Word) (r : Fin (m+1)) (hr : r.val < m)
    (pos d f : ℕ) (hend : pos + d = input.length) :
    countAt m input pos (.search r) (d + f) = countAt m input input.length (.search r) f := by
  induction d generalizing pos with
  | zero => simpa using congrArg (fun j => countAt m input j (.search r) f) hend
  | succ d ih =>
    have hpos : pos < input.length := by omega
    have hb : (atPosition input pos).head ≠ 0 := by
      rw [head_atPosition_of_lt _ _ hpos]
      split <;> decide
    rw [Nat.succ_add, countAt_step, show command m (.search r) (atPosition input pos).head =
      .move (.search r) 2 by simp [command, hr, hb]]
    change paths (machine m) (d+f) (running _ _ ((atPosition input pos).move .right) _) = _
    rw [move_right_atPosition]
    exact ih (pos+1) (by omega)

/-- If the leftward pass decides row `r`, successive passes decide their conjunction. -/
theorem check_rows {m : ℕ} (pre scan : Word) (hs : 0 < scan.length) (hit : Fin m → Prop)
    (hrow : ∀ r f, countAt m (pre ++ scan.reverse) (pre.length + scan.length - 1)
      (.tag r (tally 0)) (scan.length + f) =
      if hit r then countAt m (pre ++ scan.reverse) pre.length (.search r.succ) f else 0)
    (ticks : ℕ) (ht : m * ((pre ++ scan.reverse).length + scan.length + 1) + 1 ≤ ticks) :
    paths (machine m) ticks (initial (machine m) (pre ++ scan.reverse)) =
      (decide (∀ r, hit r)).toNat := by
  let input := pre ++ scan.reverse
  have hlen : input.length = pre.length + scan.length := by simp [input]
  have hpass (d : ℕ) (r : Fin (m+1)) (hr : r.val + d = m) (pos f : ℕ) (hpos : pos ≤ input.length)
      (hf : d * (input.length + scan.length + 1) + 1 ≤ f) :
      countAt m input pos (.search r) f = (decide (∀ i : Fin m, r.val ≤ i.val → hit i)).toNat := by
    induction d generalizing r pos f with
    | zero =>
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
      have hfull (i : Fin m) : ¬ r.val ≤ i.val := by have := i.isLt; omega
      rw [countAt_step]
      simp [command, show ¬ r.val < m by omega, hfull]
    | succ d ih =>
      have hr' : r.val < m := by omega
      let i : Fin m := ⟨r.val, hr'⟩
      let dist := input.length - pos
      let rest := f - (dist + 1 + scan.length)
      rw [Nat.succ_mul] at hf
      have hrest : d * (input.length + scan.length + 1) + 1 ≤ rest := by dsimp [rest, dist]; omega
      have htime : f = dist + ((scan.length + rest) + 1) := by dsimp [rest, dist]; omega
      rw [htime, scanRight input r hr' _ dist _ (by dsimp [dist]; omega)]
      have hdepart : countAt m input input.length (.search r) (scan.length + rest + 1) =
          countAt m input (pre.length + scan.length - 1) (.tag i (tally 0)) (scan.length + rest) := by
        let edge := pre.length + scan.length - 1
        have he : edge + 1 = input.length := by dsimp [edge]; omega
        have hb : (atPosition input (edge+1)).head = 0 := he ▸ head_atPosition_length input
        rw [← he]
        exact countAt_left (by simp [command, hb, hr', i])
      rw [hdepart, hrow i rest]
      have hc : (∀ t : Fin m, r.val ≤ t.val → hit t) ↔ hit i ∧
          ∀ t : Fin m, i.succ.val ≤ t.val → hit t := by
        constructor
        · intro hall
          exact ⟨hall i le_rfl, fun t ht => hall t (by change r.val + 1 ≤ t.val at ht; omega)⟩
        · rintro ⟨hi, hnext⟩ t ht
          by_cases he : t.val = i.val
          · exact Fin.ext he ▸ hi
          · exact hnext t (by change r.val + 1 ≤ t.val; change t.val ≠ r.val at he; omega)
      by_cases hh : hit i
      · rw [ite_eq_left hh, ih i.succ (by change (r.val+1) + d = m; omega) _ _
          (by omega) hrest]
        simp [hc, hh]
      · simp [hh, hc]
  rw [machine, initial_eq_running]
  exact (hpass m 0 (by simp) 0 ticks (Nat.zero_le _) ht).trans (by simp)

end IncidenceMachine

end VPVNP
end Computability
end OAI
