import OAI.Computability.VPVNP.RAMTapePublicExprLogValue
import OAI.Computability.VPVNP.RAMTapeUnaryWord

/-! # Finite scan for the highest set bit of a word

The scan reverses the input to inspect its most significant bit first. It emits a
unary mark for each position below the first one. For a ceiling logarithm it adds
a final mark exactly when some lower bit was set. Every consumed bit also allocates
a zero in the eventual result register.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicExprLog

open UnaryWord (Port store)
open TapeWord

/-- States for reversing the input word, locating its highest set bit, counting lower
positions, and optionally rounding up. -/
inductive Phase
  | reverse | save (bit : Bool)
  | leading | leadingZero | highZero
  | lower (seen : Bool) | lowerZero (seen : Bool) | mark (seen : Bool)
  | extra | done
  deriving DecidableEq, Fintype

/-- Scan from the highest bit, emit logarithm marks, and allocate zero bits for the result. In
ceiling mode add a mark when a lower bit is set. -/
def scan (ceiling : Bool) : StackCode Port Phase
  | .reverse => .pop .number fun b ↦ b.elim .leading .save
  | .save b => .push .tmp b .reverse
  | .leading => .pop .tmp fun b ↦ b.elim .done fun d ↦ if d then .highZero else .leadingZero
  | .leadingZero => .push .number false .leading
  | .highZero => .push .number false (.lower false)
  | .lower seen => .pop .tmp fun b ↦ b.elim (if ceiling && seen then .extra else .done)
      (fun d ↦ .lowerZero (seen || d))
  | .lowerZero seen => .push .number false (.mark seen)
  | .mark seen => .push .pending true (.lower seen)
  | .extra => .push .pending true .done
  | .done => .halt true

private abbrev zeros (n : ℕ) := List.replicate n false
private abbrev marks (n : ℕ) := List.replicate n true

private theorem upd (a x t v : List Bool) (k : Port) :
    Function.update (store [] a x [] t) k v = match k with
      | .src => store v a x [] t | .unit => store [] a x v t
      | .pending => store [] v x [] t | .number => store [] a v [] t
      | .tmp => store [] a x [] v := by
  funext j
  cases k <;> cases j <;> simp [store]

local macro "log_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_) <;>
    simp only [store, upd, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
      Option.elim_some, Option.elim_none, Bool.false_eq_true, ↓reduceIte])

private theorem reverse_run (c : Bool) (xs acc : List Bool) :
    StackRuns (scan c) (2*xs.length+1) .reverse (store [] [] xs [] acc)
      .leading (store [] [] [] [] (xs.reverse ++ acc)) := by
  induction xs generalizing acc with
  | nil => log_step; exact .nil ..
  | cons b xs ih =>
    rw [List.length_cons, Nat.mul_succ, show 2*xs.length+2+1 = (2*xs.length+1)+1+1 by omega]
    log_step
    log_step
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (b::acc)

private theorem leading_run (c : Bool) (z n : ℕ) (xs : List Bool) :
    StackRuns (scan c) (2*z) .leading (store [] [] (zeros n) [] (zeros z ++ xs))
      .leading (store [] [] (zeros (n+z)) [] xs) := by
  induction z generalizing n with
  | zero => exact .nil ..
  | succ z ih =>
    rw [Nat.mul_succ]
    change StackRuns _ _ _ (store [] [] _ [] (false :: (zeros z ++ xs))) _ _
    log_step
    log_step
    simpa only [zeros, List.replicate_succ, show n+1+z = n+(z+1) by omega] using ih (n+1)

private theorem lower_run (c seen : Bool) (xs : List Bool) (k n : ℕ) :
    ∃ t ≤ 3*xs.length+2, StackRuns (scan c) t (.lower seen) (store [] (marks k) (zeros n) [] xs)
      .done (store [] (marks (k + xs.length + (c && (seen || xs.contains true)).toNat))
        (zeros (n+xs.length)) [] []) := by
  induction xs generalizing seen k n with
  | nil =>
    cases c <;> cases seen
    all_goals first
      | exact ⟨1, by decide, by log_step; exact .nil ..⟩
      | exact ⟨2, by decide, by log_step; log_step; exact .nil ..⟩
  | cons b xs ih =>
    obtain ⟨t, ht, hr⟩ := ih (seen || b) (k+1) (n+1)
    refine ⟨t+1+1+1, by simp only [List.length_cons]; omega, ?_⟩
    log_step
    log_step
    log_step
    have hb : ((seen || b) || xs.contains true) = (seen || (b::xs).contains true) := by
      cases seen <;> cases b <;> simp
    simpa only [marks, zeros, List.length_cons, List.replicate_succ, hb,
      show k+1+xs.length = k+(xs.length+1) by omega,
      show n+1+xs.length = n+(xs.length+1) by omega] using hr

/-- The first scan produces the mathematical logarithm in unary and allocates
exactly the original number of zero result cells. -/
theorem scan_runs (c : Bool) (xs : List Bool) :
    let j := if c then Nat.clog 2 (value xs) else Nat.log 2 (value xs)
    ∃ t ≤ 5*xs.length+4, StackRuns (scan c) t .reverse (store [] [] xs [] [])
      .done (store [] (marks j) (zeros xs.length) [] []) := by
  dsimp only
  have start := reverse_run c xs []
  rw [List.append_nil] at start
  rcases split_word xs with hz | ⟨low,z,rfl⟩
  · have hv : value xs = 0 := by rw [hz]; exact UnaryWord.zeros_value _
    have rev : xs.reverse = zeros xs.length := by conv_lhs => rw [hz, List.reverse_replicate]
    rw [rev] at start
    have lead := leading_run c xs.length 0 []
    simp only [Nat.zero_add, List.append_nil] at lead
    have stop : StackRuns (scan c) 1 .leading (store [] [] (zeros xs.length) [] []) .done
        (store [] [] (zeros xs.length) [] []) := by log_step; exact .nil ..
    refine ⟨(2*xs.length+1)+2*xs.length+1, by omega, ?_⟩
    simpa only [hv, Nat.clog_zero_right, Nat.log_zero_right, ite_self, marks, List.replicate_zero] using (start.trans lead).trans stop
  · rw [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
      List.singleton_append] at start
    have lead := leading_run c z 0 (true::low.reverse)
    simp only [Nat.zero_add] at lead
    have high : StackRuns (scan c) 2 .leading (store [] [] (zeros z) [] (true::low.reverse))
        (.lower false) (store [] [] (zeros (z+1)) [] low.reverse) := by
      log_step; log_step; exact .nil ..
    obtain ⟨t, ht, hr⟩ := lower_run c false low.reverse 0 (z+1)
    simp only [List.length_reverse, Nat.zero_add, Bool.false_or, List.contains_reverse] at ht hr
    have he := ((start.trans lead).trans high).trans hr
    simp only [List.length_append, List.length_cons, List.length_replicate] at he ⊢
    rw [log_split]
    refine ⟨(2*(low.length+(z+1))+1)+2*z+2+t, by omega, ?_⟩
    simpa only [show z+1+low.length = low.length+(z+1) by omega] using he

end RAMTape.PublicExprLog

end VPVNP
end Computability
end OAI
