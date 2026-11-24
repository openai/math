import OAI.Computability.VPVNP.StructuredStackRuns
import OAI.Computability.VPVNP.StructuredStackLoop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Unary registers in a fixed bit-stack program

The validator's input offsets are natural numbers. A stack of true marks stores
such a number without placing it in the control. The routines below transfer
or add registers with an exact stack-instruction cost.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Tally

/-- A natural-number value for each tally register. -/
abbrev State (K : Type*) := K → ℕ

variable {K Q : Type*} [DecidableEq K]

/-- Represents each unary register by a stack containing one true bit per unit of its value. -/
def encode (s : State K) : Stacks K := fun k => List.replicate (s k) true

theorem encode_update (s : State K) (k : K) (v : ℕ) :
    Function.update (encode s) k (List.replicate v true) = encode (Function.update s k v) := by
  funext j
  by_cases hj : j = k <;> simp [encode, hj]

theorem increment (s : State K) (k : K) :
    (Routine.push k true).Runs 1 (encode s) (encode (Function.update s k (s k + 1))) := by
  rw [← encode_update, List.replicate_succ]
  exact Routine.runs_push k true _

/-- Loop from a unary count `n` to zero. A body runs once per mark, with its
actual cost and state allowed to vary between iterations. -/
theorem drainRuns (src : K) (body : Routine K Q) (states : ℕ → State K) (cost : ℕ → ℕ)
    (n : ℕ) (hs : ∀ i ≤ n, states i src = i)
    (hb : ∀ i < n, body.Runs (cost i) (encode (Function.update (states (i + 1)) src i))
      (encode (states i))) :
    (Routine.popLoop src (fun _ => true) body body).Runs
      (1 + ∑ i ∈ Finset.range n, (1 + cost i)) (encode (states n)) (encode (states 0)) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero]
    exact Routine.Runs.popLoop_empty src (fun _ => true) body body (by simp [encode, hs])
  | succ n ih =>
    have rest := ih (fun i hi => hs i (by omega)) (fun i hi => hb i (by omega))
    have head : encode (states (n+1)) src = true :: List.replicate n true := by
      simp [encode, hs (n+1) le_rfl, List.replicate_succ]
    have one := hb n (Nat.lt_succ_self n)
    rw [← encode_update] at one
    simpa only [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Routine.Runs.popLoop_true_continue src (fun _ => true) body body head rfl one rest

/-- Transfers marks from a source stack to a distinct destination until the source is empty,
adding its tally to the destination. -/
abbrev move (src dst : K) :=
  Routine.popLoop src (fun _ => true) (Routine.push dst true) (Routine.push dst true)

theorem move_runs (src dst : K) (hne : src ≠ dst) (s : State K) :
    (move src dst).Runs (2 * s src + 1) (encode s)
      (encode (Function.update (Function.update s src 0) dst (s dst + s src))) := by
  let f (j : ℕ) := Function.update (Function.update s src j) dst (s dst + (s src - j))
  have h := drainRuns src (Routine.push dst true) f (fun _ => 1) (s src)
    (fun i _ => by simp [f, Function.update_of_ne hne]) (by
      intro i hi
      have hi' : s src - (i+1) + 1 = s src-i := by omega
      have hstate : Function.update (Function.update (f (i+1)) src i) dst
          (Function.update (f (i+1)) src i dst + 1) = f i := by
        ext a
        by_cases he : a = dst
        · subst a
          simp [f, Function.update_of_ne hne.symm, ← hi', Nat.add_assoc]
        · by_cases ha : a = src <;> simp [f, ha, he, hne]
      rw [← hstate]
      exact increment _ _)
  have hf : f (s src) = s := by simp [f, Function.update_eq_self]
  simpa [move, hf, f, Nat.mul_comm, Nat.add_comm] using h

private abbrev scatter (src a b : K) :=
  let body := (Routine.push a true).followedBy (Routine.push b true)
  Routine.popLoop src (fun _ => true) body body

private theorem scatter_runs (src a b : K) (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (s : State K) : (scatter src a b).Runs (3*s src+1) (encode s)
    (encode (Function.update (Function.update (Function.update s src 0) a (s a+s src)) b (s b+s src))) := by
  let f (j : ℕ) := Function.update (Function.update (Function.update s src j)
    a (s a + (s src - j))) b (s b + (s src - j))
  let body := (Routine.push a true).followedBy (Routine.push b true)
  have h := drainRuns src body f (fun _ => 2) (s src)
    (fun i _ => by simp [f, hsa, hsb]) (by
      intro i hi
      let pre := Function.update (f (i+1)) src i
      let mid := Function.update pre a (pre a + 1)
      have step := (increment pre a).followedBy (increment mid b)
      have hstate : Function.update mid b (mid b + 1) = f i := by
        have hi' : s src - (i+1) + 1 = s src - i := by omega
        ext z
        by_cases hz : z = b
        · subst z
          simp [f, mid, pre, hab.symm, hsb.symm, ← hi', Nat.add_assoc]
        · by_cases ha : z = a
          · subst z
            simp [f, mid, pre, hz, hsa.symm, ← hi', Nat.add_assoc]
          · by_cases hs : z = src <;> simp [f, mid, pre, hz, ha, hs, hsa, hsb]
      rw [← hstate]
      exact step)
  have hf : f (s src) = s := by simp [f, Function.update_eq_self]
  simpa [scatter, body, hf, f, Nat.mul_comm, Nat.add_comm] using h

/-- Preserve the source while adding its contents to the destination. -/
abbrev copyAdd (src dst tmp : K) := (move src tmp).followedBy (scatter tmp src dst)

theorem copyAdd_runs (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : State K) (ht : s tmp = 0) : (copyAdd src dst tmp).Runs (5*s src+2)
      (encode s) (encode (Function.update s dst (s dst+s src))) := by
  let m := Function.update (Function.update s src 0) tmp (s tmp + s src)
  have first := move_runs src tmp hst s
  have second := scatter_runs tmp src dst hst.symm hdt.symm hsd m
  have hfinal : Function.update (Function.update (Function.update m tmp 0) src (m src+m tmp)) dst
      (m dst+m tmp) = Function.update s dst (s dst+s src) := by
    ext a
    by_cases ha : a = dst
    · subst a
      simp [m, ht, hdt, hsd.symm]
    · by_cases h₁ : a = src
      · subst a
        simp [m, ht, ha, hst]
      · by_cases h₂ : a = tmp <;> simp [m, ht, ha, h₁, h₂, hst.symm, hdt.symm]
  rw [hfinal] at second
  have hcost : 2*s src+1 + (3*m tmp+1) = 5*s src+2 := by simp [m, ht]; omega
  rw [← hcost]
  exact first.followedBy second

end RAMTape.Tally

end VPVNP
end Computability
end OAI
