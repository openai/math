import OAI.Computability.VPVNP.RankQueryTimeBounds
import OAI.Computability.VPVNP.RankQueryExecutionSpace
import OAI.Computability.VPVNP.RankCursorSchurSpace

/-!
# Rank resources with a separately bounded scalar-entry routine

The expensive descriptor's time bound is allowed in the query clock. Its
space bound enters the maximum with the cubic bound on the short local
actions, binary registers, and suspended Schur frames.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

/-- A uniform exponential clock still suffices when the descriptor has a
larger time budget than the remaining Schur actions. -/
theorem rankReadTime_le_exp (n m Bd B w v e s : ℕ)
    (hn : n ≤ 2^s) (hm : m ≤ 2^s) (hd : Bd ≤ 2^s) (hB : B ≤ 2^s)
    (hw : w ≤ 2^s) (hv : v ≤ 2^s) (he : e ≤ 2^s) :
    let Z := (n+m)*n
    ((n+1)*(Z+1))*(readClock n n Z Bd B w v e+checkClock w v e+1)+2 ≤
      2^((4*s+10)*(4*s+7)+5*s+20) := by
  let Z := (n+m)*n
  have hlocal : Engine.boundedStepTime Bd B w v e ≤ Engine.stepBudget (max Bd B) w v e := by
    unfold Engine.boundedStepTime Engine.stepBudget
    omega
  have hread : readClock n n Z Bd B w v e ≤ rootQueryClock n n Z (max Bd B) w v e :=
    Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left (SchurKey.clock n n Z) hlocal) _) _
  apply le_trans _ (rankTime_le_exp n m (max Bd B) w v e s hn hm (max_le hd hB) hw hv he)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right hread _) _)) _

/-- If the matrix row count fits in `s` bits, space outside the descriptor is
bounded by a cubic polynomial in the local widths, auxiliary space, and
short-action budget. The descriptor's own space bound remains separate. -/
theorem rankReadSpace_le (n s S A B w v e : ℕ) (hn : n ≤ 2^s) :
    outerRankSpace (readSpace n n S A B w v e) A w v e ≤
      max (S+1) (32768*(s+A+B+w+v+e+1)^3) := by
  let M := s+A+B+w+v+e+1
  have hp : 1 ≤ M := by dsimp [M]; omega
  have hs : s ≤ M := by dsimp [M]; omega
  have ha : A ≤ M := by dsimp [M]; omega
  have hb : B ≤ M := by dsimp [M]; omega
  have hw : w ≤ M := by dsimp [M]; omega
  have hv : v ≤ M := by dsimp [M]; omega
  have he : e ≤ M := by dsimp [M]; omega
  have hm₂ : M ≤ M^2 := by simpa [pow_two] using Nat.mul_le_mul_left M hp
  have hm₃ : M^2 ≤ M^3 := Nat.pow_le_pow_right hp (by decide)
  have hev : e*v ≤ M^2 := by simpa only [pow_two] using Nat.mul_le_mul he hv
  have hmax : max 1 (max w (e*v)) ≤ M^2 := by omega
  have hdepth := Nat.clog_le_of_le_pow hn
  have hhistory : (Nat.clog 2 n+4+Nat.clog 2 n)*(2*max 1 (max w (e*v))+1) ≤ 18*M^3 := calc
    _ ≤ (6*M)*(3*M^2) := Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by ring
  have hlocal : Engine.stepBudget B w v e ≤ 224*M^2 := by unfold Engine.stepBudget; omega
  have hschur : Engine.runSpace A (Nat.clog 2 n+4+Nat.clog 2 n) B w v e ≤ 242*M^3 := by
    unfold Engine.runSpace
    omega
  have hload : loadClock w ≤ 43*M := by unfold loadClock; omega
  have hsq : (w+1)^2 ≤ 4*M^2 := calc
    _ ≤ (2*M)^2 := Nat.pow_le_pow_left (by omega) 2
    _ = _ := by ring
  have hcheck : checkClock w v e ≤ 29242*M^2 := by unfold checkClock; rw [Registers.clock_eq]; omega
  change _ ≤ max (S+1) (32768*M^3)
  have hprep : max w A + loadClock w ≤ 32768*M^3 := by
    have hx := max_le hw ha
    omega
  have hcap : Engine.boundedSpace S A (Nat.clog 2 n+4+Nat.clog 2 n) B w v e ≤
      max (S+1) (32768*M^3) :=
    max_le_max le_rfl (hschur.trans (Nat.mul_le_mul_right _ (by decide)))
  have htail : A+w+e*v+1+checkClock w v e ≤ 32768*M^3 := by omega
  exact max_le (max_le (hprep.trans (le_max_right ..)) hcap) (htail.trans (le_max_right ..))

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
