import OAI.Hierarchy.DescentPublicDegreeNumbers
import OAI.Hierarchy.DescentGrainCalendar
import OAI.Hierarchy.DescentStageLedger

namespace OAI
/-! # Uniform first-stage rates before the terminal cutoff is selected -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty
variable {F : Type} [Field F]

theorem first_argument_count (S : AtomSchedule) (b p : ℕ) (positive : 0 < p) :
    S.firstWidth b p/p=b^(S.rounds*S.height)*b :=by
  simp [AtomSchedule.firstWidth,AtomSchedule.grainAt,AtomSchedule.ordinaryDone,Nat.mul_assoc,positive.ne']

theorem grainRate (b t J : ℕ) :
    b^(t*J)*b ≤ scale J (Nat.clog 2 b*(t+1)) :=by
  have p:=Nat.le_pow_clog (by decide : 1 < 2) b
  calc
    b^(t*J)*b=b^(t*J+1) := (pow_succ ..).symm
    _ ≤ (2^Nat.clog 2 b)^(t*J+1) := Nat.pow_le_pow_left p _
    _ ≤ _:=by
      rw [←pow_mul]
      apply Nat.pow_le_pow_right (by decide)
      calc
        _ ≤ Nat.clog 2 b*((t+1)*(J+1)) := Nat.mul_le_mul_left _ (by nlinarith)
        _=_:=by ring

theorem groupRateAt (t J host cap cut : ℕ) :
    2^(groupBits t J host cap cut) ≤ scale J (1+(host+cap)*(t+1)+8+cut) :=
  Nat.pow_le_pow_right (by decide) (groupBits_linear ..)

/-- The numerical public search always returns one of the fixed finite
round degrees, including its default at a reset-only initial age. -/
def initialDegreeMax : ℕ → ℕ
  | 0=>0
  | t+1=>max (DescentCompiler.atRound t) (initialDegreeMax t)

private theorem degree_search (target t : ℕ) :
    ((Chronology.OrdinaryLink.roundFor target t).elim 0 DescentCompiler.atRound) ≤ initialDegreeMax t :=by
  induction t with
  | zero=>rfl
  | succ t ih=>
    unfold Chronology.OrdinaryLink.roundFor initialDegreeMax
    split
    · exact Nat.le_max_left ..
    · exact ih.trans (Nat.le_max_right ..)

theorem seed_degree (t b factor : ℕ) : Chronology.OrdinaryLink.publicDegree t b factor ≤ initialDegreeMax t :=
  degree_search _ _

/-- A logarithm of the real CPU height is only linear in the chosen public
epoch, with the explicit constant allowed to depend on B. -/
theorem log_height (h B : ℕ) (positive : 0 < B) :
    Nat.log 2 h+1 ≤ (2*B)*(Nat.log 2 h/(2*B)+1) :=by
  let z:=Nat.log 2 h
  have pos : 0 < 2*B :=by omega
  have up : z < (z/(2*B)+1)*(2*B) :=(Nat.div_lt_iff_lt_mul pos).mp (Nat.lt_succ_self _)
  simpa only [z,Nat.mul_comm (2*B)] using (Nat.succ_le_of_lt up)

end Hierarchy.DescentDatedSeedStartup

end OAI
