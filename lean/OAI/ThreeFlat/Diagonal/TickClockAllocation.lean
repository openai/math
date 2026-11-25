import OAI.ThreeFlat.Diagonal.TickChronology
import OAI.ThreeFlat.Diagonal.GroupCount

namespace OAI
/-! # The seven-phase clock at the diagonal theorem's dyadic parameters -/

namespace ThreeFlat.Diagonal.TickChronology

/-- A quarter of the clock contains one evaluation budget per group; a
group itself occupies twice that budget. -/
def reserve {T J C E : ℕ} (jpos : 0 < J) (cpos : 0 < C)
    (room : C+2 ≤ E) (exactT : T = 4*(J*E)) : Clock where
  beginTick := T/4
  groups := J
  groupDuration := 2*E
  chunks := C
  evaluateTicks := E
  last := T-1
  begin_pos := by
    rw [exactT,Nat.mul_div_cancel_left _ (by decide)]
    exact Nat.mul_pos jpos (by omega)
  chunks_pos := cpos
  room := by omega
  fits := by
    have epos : 0 < E := by omega
    have pos := Nat.mul_pos jpos epos
    rw [exactT,Nat.mul_div_cancel_left _ (by decide)]
    rw [show J*(2*E) = 2*(J*E) by ring]
    omega

theorem clock_budget {w J C : ℕ} (hw : 6 ≤ w) (jp : ∃ m : ℕ, J = 2^m)
    (bound : J ≤ 2^(2*w^4)) (_cp : 0 < C) (small : C ≤ J) :
    let T := 2^(w^6)
    let E := T/(4*J)
    0 < J ∧ C+2 ≤ E ∧ T = 4*(J*E) := by
  intro T E
  obtain ⟨m,rfl⟩ := jp
  have hm := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp bound
  have h45 : 6*w^4 ≤ w^5 := by
    rw [pow_succ w 4,Nat.mul_comm 6 (w^4)]
    exact Nat.mul_le_mul_left (w^4) hw
  have h56 : w^5 ≤ w^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hw4 : 6 ≤ w^4 := hw.trans (Nat.le_self_pow (by decide) _)
  have hdiff : m+2 ≤ w^6-(2+m) := by omega
  have add : 2+m+(w^6-(2+m)) = w^6 := by omega
  have fac : 4*(2^m) = 2^(2+m) := (Nat.pow_add 2 2 m).symm
  have ev : E = 2^(w^6-(2+m)) := by
    change 2^(w^6)/(4*2^m) = _
    rw [fac,Nat.pow_div (by omega) (by decide)]
  have hg := Nat.pow_le_pow_right (by decide : 0 < 2) hdiff
  have p := Nat.two_pow_pos m
  rw [pow_add] at hg
  rw [ev]
  refine ⟨p,by omega,?_⟩
  change 2^(w^6) = 4*(2^m * 2^(w^6-(2+m)))
  rw [← Nat.mul_assoc,fac,← pow_add,add]

/-- The chronological construction uses the public number of transitions,
the established group budget, and the physical external chunk count. -/
def dyadicClock {w J C : ℕ} (hw : 6 ≤ w) (jp : ∃ m : ℕ, J = 2^m)
    (bound : J ≤ 2^(2*w^4)) (cp : 0 < C) (small : C ≤ J) : Clock :=
  let h := clock_budget hw jp bound cp small
  reserve h.1 cp h.2.1 h.2.2

end ThreeFlat.Diagonal.TickChronology

end OAI
