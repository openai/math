import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Computing a unary bucket size from the rounded binary exponent

The denominator is fixed in the finite control. For each nonempty block of at
most `q` input bits the machine doubles its unary output, using a third stack
temporarily. Every instruction reads or writes a single stack bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputBucket

/-- Stack labels for the logarithm marks, unary bucket, and temporary doubling stack. -/
inductive Port
  | src | out | tmp
  deriving DecidableEq

instance : Fintype Port :=
  ⟨{.src, .out, .tmp}, fun p => by cases p <;> simp⟩

/-- States that double the unary bucket once per block and count the remaining skips within a
block of size at most the fixed denominator. -/
inductive State (q : ℕ)
  | init | block | copy | pushFirst | pushSecond | restore | putBack | skip (r : Fin q) | done
  deriving DecidableEq, Fintype

/-- Start with one bucket mark and double its unary value once for every nonempty block of at
most the denominator’s number of input marks. -/
def code (q : ℕ) (hq : 0 < q) : StackCode Port (State q)
  | .init => .push .out true .block
  | .block => .pop .src (fun b => b.elim .done (fun _ => .copy))
  | .copy => .pop .out (fun b => b.elim .restore (fun _ => .pushFirst))
  | .pushFirst => .push .tmp true .pushSecond
  | .pushSecond => .push .tmp true .copy
  | .restore => .pop .tmp (fun b => b.elim (.skip ⟨q - 1, by omega⟩) (fun _ => .putBack))
  | .putBack => .push .out true .restore
  | .skip r => if r.val = 0 then .goto .block else
      .pop .src (fun b => b.elim .block (fun _ => .skip ⟨r.val - 1, by have := r.isLt; omega⟩))
  | .done => .halt true

/-- Represent the input, output, and scratch tallies of the bucket routine as stacks of true
bits. -/
def store (src out tmp : ℕ) : Stacks Port
  | .src => List.replicate src true
  | .out => List.replicate out true
  | .tmp => List.replicate tmp true

private theorem set_store (src out tmp v : ℕ) (k : Port) :
    Function.update (store src out tmp) k (List.replicate v true) = match k with
      | .src => store v out tmp
      | .out => store src v tmp
      | .tmp => store src out v := by
  cases k <;> funext j <;> cases j <;> simp [store]

variable {q : ℕ} (hq : 0 < q)

private theorem pop_src_succ {n a t : ℕ} {s : State q} {f}
    (h : code q hq s = .pop .src f) :
    StackStep (code q hq) s (store (n + 1) a t) (f (some true)) (store n a t) := by
  simpa only [store, List.replicate_succ, List.head?_cons, List.tail_cons, set_store]
    using StackStep.pop (s := store (n + 1) a t) h

private theorem pop_src_zero {a t : ℕ} {s : State q} {f}
    (h : code q hq s = .pop .src f) :
    StackStep (code q hq) s (store 0 a t) (f none) (store 0 a t) := by
  have he := StackStep.pop (s := store 0 a t) h
  change StackStep _ _ _ (f none) (Function.update (store 0 a t) .src (List.replicate 0 true)) at he
  simpa only [set_store] using he

private theorem pop_out_succ {n a t : ℕ} {s : State q} {f}
    (h : code q hq s = .pop .out f) :
    StackStep (code q hq) s (store n (a + 1) t) (f (some true)) (store n a t) := by
  simpa only [store, List.replicate_succ, List.head?_cons, List.tail_cons, set_store]
    using StackStep.pop (s := store n (a + 1) t) h

private theorem pop_tmp_succ {n a t : ℕ} {s : State q} {f}
    (h : code q hq s = .pop .tmp f) :
    StackStep (code q hq) s (store n a (t + 1)) (f (some true)) (store n a t) := by
  simpa only [store, List.replicate_succ, List.head?_cons, List.tail_cons, set_store]
    using StackStep.pop (s := store n a (t + 1)) h

private theorem push_tmp {n a t : ℕ} {s s' : State q} (h : code q hq s = .push .tmp true s') :
    StackStep (code q hq) s (store n a t) s' (store n a (t + 1)) := by
  have he := StackStep.push (s := store n a t) h
  change StackStep _ _ _ _ (Function.update (store n a t) .tmp (List.replicate (t+1) true)) at he
  simpa only [set_store] using he

private theorem push_out {n a t : ℕ} {s s' : State q} (h : code q hq s = .push .out true s') :
    StackStep (code q hq) s (store n a t) s' (store n (a + 1) t) := by
  have he := StackStep.push (s := store n a t) h
  change StackStep _ _ _ _ (Function.update (store n a t) .out (List.replicate (a+1) true)) at he
  simpa only [set_store] using he

private theorem copy_run (n a t : ℕ) :
    StackRuns (code q hq) (3*a+1) .copy (store n a t) .restore (store n 0 (t+2*a)) := by
  induction a generalizing t with
  | zero =>
    have he := StackStep.pop (s := store n 0 t) (show code q hq .copy = .pop .out _ from rfl)
    change StackStep (code q hq) _ _ .restore (Function.update (store n 0 t) .out (List.replicate 0 true)) at he
    simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, set_store] using
      StackRuns.cons he (StackRuns.nil _ _)
  | succ a ih =>
    have h := StackRuns.cons (pop_out_succ hq (show code q hq .copy = .pop .out _ from rfl))
      (StackRuns.cons (push_tmp hq (show code q hq .pushFirst = .push .tmp true _ from rfl))
      (StackRuns.cons (push_tmp hq (show code q hq .pushSecond = .push .tmp true _ from rfl))
      (ih (t + 1 + 1))))
    convert h using 1
    congr 1
    omega

private theorem restore_run (n a t : ℕ) :
    StackRuns (code q hq) (2*t+1) .restore (store n a t) (.skip ⟨q-1, by omega⟩) (store n (a+t) 0) := by
  induction t generalizing a with
  | zero =>
    have he := StackStep.pop (s := store n a 0) (show code q hq .restore = .pop .tmp _ from rfl)
    change StackStep (code q hq) _ _ (.skip ⟨q-1, by omega⟩)
      (Function.update (store n a 0) .tmp (List.replicate 0 true)) at he
    simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, set_store] using
      StackRuns.cons he (StackRuns.nil _ _)
  | succ t ih =>
    have h := StackRuns.cons (pop_tmp_succ hq (show code q hq .restore = .pop .tmp _ from rfl))
      (StackRuns.cons (push_out hq (show code q hq .putBack = .push .out true _ from rfl)) (ih (a+1)))
    convert h using 1
    congr 1
    omega

private theorem skip_run (r : Fin q) (n a : ℕ) : ∃ u ≤ r.val + 1,
    StackRuns (code q hq) u (.skip r) (store n a 0) .block (store (n-r.val) a 0) := by
  obtain ⟨r,hr⟩ := r
  induction r generalizing n with
  | zero =>
    refine ⟨1, le_rfl, ?_⟩
    exact .cons (.goto (by simp [code])) (.nil ..)
  | succ r ih =>
    have hc : code q hq (.skip ⟨r+1,hr⟩) = .pop .src
        (fun b => b.elim .block (fun _ => .skip ⟨r, by omega⟩)) := by simp [code]
    cases n with
    | zero =>
      refine ⟨1, by simp, ?_⟩
      simp only [Nat.zero_sub]
      exact .cons (pop_src_zero hq hc) (.nil ..)
    | succ n =>
      obtain ⟨u, hu, run⟩ := ih n (by omega)
      refine ⟨u+1, by simp at hu ⊢; omega, ?_⟩
      simpa using StackRuns.cons (pop_src_succ hq hc) run

private def rounds (k q : ℕ) := (k + (q - 1)) / q

private theorem rounds_zero (hq : 0 < q) : rounds 0 q = 0 := by
  simp only [rounds, Nat.zero_add]
  exact Nat.div_eq_of_lt (by omega)

private theorem rounds_succ (hq : 0 < q) (k : ℕ) : rounds (k+1) q = rounds (k - (q-1)) q + 1 := by
  unfold rounds
  by_cases h : q - 1 ≤ k
  · have h₁ : k + 1 + (q - 1) = k + q := by omega
    have h₂ : k - (q - 1) + (q - 1) = k := by omega
    rw [h₁, h₂, Nat.add_div_right _ hq]
  · have h₁ : k + 1 + (q - 1) = k + q := by omega
    have h₂ : k - (q - 1) = 0 := by omega
    rw [h₁, h₂, Nat.zero_add, Nat.add_div_right _ hq, Nat.div_eq_of_lt (by omega : k < q),
      Nat.div_eq_of_lt (by omega : q-1 < q)]

private theorem loop_run (k a : ℕ) : ∃ t ≤ (k+1)*(q+10)*(a * 2^rounds k q+1),
    StackRuns (code q hq) t .block (store k a 0) .done (store 0 (a * 2^rounds k q) 0) := by
  induction k using Nat.strong_induction_on generalizing a with
  | h k ih =>
    cases k with
    | zero =>
      rw [rounds_zero hq, pow_zero, Nat.mul_one]
      refine ⟨1, Nat.succ_le_iff.mpr (by positivity), ?_⟩
      exact .cons (pop_src_zero hq (show code q hq .block = .pop .src _ from rfl)) (.nil ..)
    | succ k =>
      let r := k - (q-1)
      have hr : r < k+1 := by dsimp [r]; omega
      obtain ⟨s, hs, scan⟩ := skip_run hq ⟨q-1, by omega⟩ k (2*a)
      have hfirst := StackRuns.cons (pop_src_succ hq (show code q hq .block = .pop .src _ from rfl))
        (((copy_run hq k a 0).trans (by simpa using restore_run hq k 0 (2*a))).trans scan)
      obtain ⟨t,ht,run⟩ := ih r hr (2*a)
      have he : a*2^rounds (k+1) q = (2*a)*2^rounds r q := by
        rw [rounds_succ hq, pow_succ]; dsimp [r]; ring
      rw [he]
      refine ⟨_, ?_, hfirst.trans run⟩
      have hs' : s ≤ q := by change s ≤ q-1+1 at hs; omega
      let A := (2*a)*2^rounds r q+1
      have ha : a ≤ A := by
        have he' := Nat.mul_le_mul_left (2*a) (Nat.one_le_two_pow (n := rounds r q))
        dsimp [A]
        omega
      have hround : (3*a+1 + (2*(2*a)+1) + s + 1) ≤ (q+10)*A := by
        have h₁ := Nat.mul_le_mul_left 10 ha
        have h₂ := Nat.mul_le_mul_left q (by dsimp [A]; omega : 1 ≤ A)
        rw [Nat.add_mul]
        dsimp [A] at *
        omega
      have hremain : t ≤ (k+1)*(q+10)*A :=
        ht.trans (Nat.mul_le_mul_right A (Nat.mul_le_mul_right (q+10) (by omega)))
      calc
        _ ≤ (q+10)*A + (k+1)*(q+10)*A := Nat.add_le_add hround hremain
        _ = _ := by ring

/-- From initially empty work stacks, compute the unary bucket size and clear the input. -/
theorem bucket_run (q k : ℕ) (hq : 0 < q) :
    ∃ t ≤ (k+1)*(q+10)*(2^((k+(q-1))/q)+1)+1,
      StackRuns (code q hq) t .init (store k 0 0) .done (store 0 (2^((k+(q-1))/q)) 0) := by
  obtain ⟨t, ht, h⟩ := loop_run hq k 1
  simp only [Nat.one_mul, rounds] at ht h
  exact ⟨t+1, Nat.add_le_add_right ht 1,
    .cons (push_out hq (show code q hq .init = .push .out true _ from rfl)) h⟩

end RAMTape.InputBucket

end VPVNP
end Computability
end OAI
