import OAI.Computability.VPVNP.ChoiceWitness
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Int

/-!
# The signed path count in §2.2

We use the self-delimiting two-tape program format of `VPVNP.UniversalMachine`. A halt in
state one returns minus one when the work tape head reads binary one (symbol two), and plus
one otherwise. State zero, malformed inputs and timeouts return zero. A Boolean string has
one slot per tick. At deterministic steps and after a halt, only zero is valid padding.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open VPVNP.UniversalMachine

/-- Signed output observed at the end of a clocked run. -/
def haltOutput {extra : ℕ} (c : Config extra) : ℤ :=
  if c.state.val = 1 then (if c.secondTape.head = 2 then -1 else 1) else 0

/-- Sum of the signed leaves in the binary computation tree, including a halt at time zero. -/
def signedPaths (p : Program) : ℕ → Config p.extra → ℤ
  | 0, c => haltOutput c
  | fuel + 1, c =>
    if c.state.val = 1 then haltOutput c else if c.state.val = 0 then 0 else
      match branches p c with
      | .stop => 0
      | .one a => signedPaths p fuel (advance c a)
      | .two a b => signedPaths p fuel (advance c a) + signedPaths p fuel (advance c b)

private theorem signedPaths_halt (p : Program) (t : ℕ) (c : Config p.extra)
    (h : c.state.val = 1) : signedPaths p t c = haltOutput c := by
  cases t <;> simp [signedPaths, h]

private theorem signedPaths_reject (p : Program) (t : ℕ) (c : Config p.extra)
    (h : c.state.val = 0) : signedPaths p t c = 0 := by
  cases t <;> simp [signedPaths, haltOutput, h]

private theorem signedPaths_succ (p : Program) (t : ℕ) (c : Config p.extra) :
    signedPaths p (t + 1) c =
      signedPaths p t (choiceStep p c false) + signedPaths p t (choiceStep p c true) := by
  have hbad := signedPaths_reject p t (reject c) rfl
  by_cases ha : c.state.val = 1
  · simp [signedPaths, choiceStep, ha, hbad, signedPaths_halt p t c ha]
  by_cases hr : c.state.val = 0
  · simp [signedPaths, choiceStep, hr, signedPaths_reject p t c hr]
  cases h : branches p c <;> simp [signedPaths, choiceStep, ha, hr, h, hbad]

/-- One canonical zero-padded choice string per path, weighted by the output of that path. -/
theorem signedPaths_eq_sum (p : Program) (t : ℕ) (c : Config p.extra) :
    signedPaths p t c =
      ∑ w : Fin t → Bool, haltOutput ((List.ofFn w).foldl (choiceStep p) c) := by
  induction t generalizing c with
  | zero => simp [signedPaths]
  | succ t ih =>
    rw [signedPaths_succ, ih, ih,
      ← (Fin.consEquiv (fun _ : Fin (t + 1) => Bool)).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    simp [Fin.consEquiv]

/-- A single deterministically verified witness for the coefficient of input `x`. -/
def signedWitness {n : ℕ} (x : Fin n → Bool) (w : Fin (n ^ 100) → Bool) : ℤ :=
  match decode (List.ofFn x) with
  | none => 0
  | some p => haltOutput ((List.ofFn w).foldl (choiceStep p) (initial p (List.ofFn x)))

/-- The integer coefficient `U*_n(x)` in (2.1) of the border-circuit paper. -/
def signedCount {n : ℕ} (x : Fin n → Bool) : ℤ :=
  match decode (List.ofFn x) with
  | none => 0
  | some p => signedPaths p (n ^ 100) (initial p (List.ofFn x))

/-- The signed path sum is an ordinary finite Boolean witness sum over the integers. -/
theorem signedCount_eq_sum_witnesses {n : ℕ} (x : Fin n → Bool) :
    signedCount x = ∑ w, signedWitness x w := by
  cases h : decode (List.ofFn x) <;> simp [signedCount, signedWitness, h, signedPaths_eq_sum]

/-- A witness is weighted by one of the three allowed signed outputs. -/
theorem abs_signedWitness_le {n : ℕ} (x : Fin n → Bool) (w : Fin (n ^ 100) → Bool) :
    |signedWitness x w| ≤ 1 := by
  cases h : decode (List.ofFn x) <;> simp only [signedWitness, h, haltOutput]
  · decide
  · split_ifs <;> decide

/-- The verifier returns exactly one of the three output labels permitted by the manuscript. -/
theorem signedWitness_values {n : ℕ} (x : Fin n → Bool) (w : Fin (n ^ 100) → Bool) :
    signedWitness x w = 0 ∨ signedWitness x w = 1 ∨ signedWitness x w = -1 :=
  Int.abs_le_one_iff.mp (abs_signedWitness_le x w)

/-- The coefficient magnitude bound from §2.2, with binary branching and clock `n^100`. -/
theorem abs_signedCount_le {n : ℕ} (x : Fin n → Bool) :
    |signedCount x| ≤ 2 ^ (n ^ 100) := by
  rw [signedCount_eq_sum_witnesses]
  calc
    _ ≤ ∑ w, |signedWitness x w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w : Fin (n ^ 100) → Bool, (1 : ℤ) :=
      Finset.sum_le_sum fun w _ => abs_signedWitness_le x w
    _ = _ := by simp

/-- On a nonempty all-zero input the empty program halts immediately with output plus one. -/
theorem signedCount_allFalse {n : ℕ} (hn : 0 < n) :
    signedCount (fun _ : Fin n => false) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [signedCount, List.ofFn_succ, decode_false_cons]
  rw [signedPaths_halt _ _ _ rfl]
  rfl

end BorderVNP
end Computability
end OAI
