import OAI.Computability.VPVNP.RankQueryStackCodegen
import OAI.Computability.VPVNP.DeterminantQueries

/-!
# Descending bidegree scan for rank

The scan asks for one coefficient at a time and returns the first outer degree
with a nonzero coefficient. One transition updates the two indices, or halts
with the exact rank. Its fixed bit-stack code receives the zero-test flag
from the scalar routine.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open Dispatch BurstRAM RAMTape

/-- State of the descending coefficient search, recording a current rank and degree or the
finished rank. -/
inductive State where
  | running (u z : ℕ)
  | done (rank : ℕ)
  deriving DecidableEq

/-- Return the current rank for a nonzero coefficient. On zero, move to the previous degree or
restart at degree `Z` for the previous rank. -/
def advance (Z u z : ℕ) (zero : Bool) : State :=
  if zero then
    if z = 0 then if u = 0 then .done 0 else .running (u-1) Z
    else .running u (z-1)
  else .done u

/-- Perform one coefficient test on a running cursor and keep a finished cursor at its recorded
rank. -/
def step (q : ℕ → ℕ → Bool) (Z : ℕ) : State → State
  | .running u z => advance Z u z (q u z)
  | .done r => .done r

/-- Six-output dispatch tree implementing one transition of the descending rank cursor. -/
def control : Code :=
  let zero : Expr := .reg 0
  let u : Expr := .reg 1
  let z : Expr := .reg 2
  let Z : Expr := .reg 3
  .test zero 0 (.emit ![1,u,0,0,0,0]) <|
    .test z 0 (.test u 0 (.emit ![1,0,0,0,0,0]) (.emit ![0,u-1,Z,0,0,0])) (.emit ![0,u,z-1,0,0,0])

/-- Encode the zero-test result, current rank, current degree and degree limit in the cursor's
eight input words. -/
def input (Z u z : ℕ) (zero : Bool) : Fin 8 → ℕ := ![zero.toNat,u,z,Z,0,0,0,0]

/-- Encode a running cursor or final rank as six output words with the status tag first. -/
def State.words : State → Fin 6 → ℕ
  | .running u z => ![0,u,z,0,0,0]
  | .done r => ![1,r,0,0,0,0]

theorem control_eq (Z u z : ℕ) (zero : Bool) :
    control.eval (input Z u z zero) = (advance Z u z zero).words := by
  cases zero <;> by_cases hz : z = 0 <;> by_cases hu : u = 0 <;>
    funext i <;> fin_cases i <;>
    simp [control, Code.eval, Expr.eval, eval_sub, input, advance, State.words, hz, hu]

/-- Maximum of the first `n` values of a natural-valued stream, starting from zero. -/
def peak (f : ℕ → ℕ) (n : ℕ) : ℕ := streamMaximum n fun i => f i.val

theorem peak_succ (f : ℕ → ℕ) (n : ℕ) : peak f (n+1) = max (peak f n) (f n) := by
  simp only [peak, streamMaximum, Fin.foldl_succ_last, Fin.val_castSucc, Fin.val_last]

/-- Contribution of rank `u` from the first `count` degree tests, equal to `u` if any
coefficient is nonzero. -/
def row (q : ℕ → ℕ → Bool) (u : ℕ) (count : ℕ) := peak (fun z => if q u z then 0 else u) count

/-- Largest candidate rank strictly below `u` for which the zero test fails at some degree from
zero through `Z`, defaulting to zero. -/
def below (q : ℕ → ℕ → Bool) (Z u : ℕ) := peak (fun i => row q i (Z+1)) u

/-- Rank represented by the cursor, taking the maximum over the remaining search region or
returning the finished value. -/
def answer (q : ℕ → ℕ → Bool) (Z : ℕ) : State → ℕ
  | .running u z => max (below q Z u) (row q u (z+1))
  | .done r => r

private theorem row_le (q : ℕ → ℕ → Bool) (u count : ℕ) : row q u count ≤ u :=
  (streamMaximum_le_iff count u (fun i => if q u i.val then 0 else u)).mpr fun i => by split_ifs <;> omega

private theorem below_le (q : ℕ → ℕ → Bool) (Z u : ℕ) : below q Z u ≤ u :=
  (streamMaximum_le_iff ..).mpr fun i => (row_le q i (Z+1)).trans i.isLt.le

theorem answer_step (q : ℕ → ℕ → Bool) (Z : ℕ) (s : State) :
    answer q Z (step q Z s) = answer q Z s := by
  cases s with
  | done => rfl
  | running u z =>
    cases h : q u z with
    | false =>
      simp only [step, h, advance, Bool.false_eq_true, ite_false, answer, row, peak_succ]
      change u = max (below q Z u) (max (row q u z) u)
      rw [max_eq_right (row_le q u z), max_eq_right (below_le q Z u)]
    | true =>
      cases z with
      | succ z =>
        simp only [step, h, advance, ite_true, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one, answer, row, peak_succ, max_zero]
      | zero =>
        cases u with
        | zero => simp [step, h, advance, answer, below, row, peak, streamMaximum]; rfl
        | succ u =>
          simp only [step, h, advance, ite_true, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one, answer,
            below, row, peak_succ]
          simp [peak, streamMaximum]

/-- Exact number of remaining requests if all remaining coefficients vanish. -/
def remaining (Z : ℕ) : State → ℕ
  | .running u z => u*(Z+1)+z+1
  | .done _ => 0

theorem remaining_decreases (q : ℕ → ℕ → Bool) (Z u z : ℕ) :
    remaining Z (step q Z (.running u z)) < remaining Z (.running u z) := by
  cases h : q u z <;> cases z <;> cases u <;> simp [step, advance, h, remaining, Nat.succ_mul]

/-- Deterministic recursion asks for at most the entire rectangle of scalar
queries. Its halting value is the maximum nonzero outer degree. -/
theorem run (q : ℕ → ℕ → Bool) (Z : ℕ) (s : State) :
    ∃ t ≤ remaining Z s, (step q Z)^[t] s = .done (answer q Z s) := by
  induction s using (measure (remaining Z)).wf.induction with
  | h s ih =>
    cases s with
    | done r => exact ⟨0, le_rfl,rfl⟩
    | running u z =>
      have ht := remaining_decreases q Z u z
      obtain ⟨t,hclock,hrun⟩ := ih _ ht
      refine ⟨t+1, by omega, ?_⟩
      change (step q Z)^[t] (step q Z (.running u z)) = .done (answer q Z (.running u z))
      rw [hrun, answer_step]

theorem initial_answer {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) F) (get : ℕ → ℕ → F)
    (hg : ∀ u z, get u z = ((rankPolynomial M).coeff u).coeff z) :
    let Z := (n+m)*n
    answer (fun u z => decide (get u z = 0)) Z (.running n Z) = M.rank := by
  let Z := (n+m)*n
  let q := fun u z => decide (get u z = 0)
  have hs := scanRank_correct M get hg
  change max (below q Z n) (row q n (Z+1)) = _
  rw [below, ← peak_succ (fun u => row q u (Z+1)) n]
  simpa [scanRank, peak, row, q, Z] using hs

/-- All index updates and the stopping decision on one scalar zero-test flag
run on a fixed binary-stack routine. -/
theorem physical {w p : ℕ} (Z u z : ℕ) (zero : Bool)
    (rs : Regs (14+control.scratch) w) (hw : (p+1)*control.wordFactor ≤ w)
    (he : ∀ i, input Z u z zero i < 2^p)
    (hr : ∀ i, (rs (Code.inReg control.scratch i)).val = input Z u z zero i)
    (pub : Fin 0 → Word w) (persistent : Word w) :
    ∃ t ≤ (control.emitFields control.scratch (List.finRange 6)).length * (100*(w+1)^2), ∃ out,
      (control.physical control.scratch).Runs t (ISA.bank pub persistent rs []) (ISA.bank pub persistent out []) ∧
      (fun i => (out (Code.outReg control.scratch i)).val) = (advance Z u z zero).words := by
  obtain ⟨t,ht,out,hrun,_,hvalue⟩ := control.physical_runs _ _ le_rfl _ _ hw he hr pub persistent
  exact ⟨t,ht,out,hrun,(funext hvalue).trans (control_eq ..)⟩

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
