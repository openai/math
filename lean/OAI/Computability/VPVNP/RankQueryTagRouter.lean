import OAI.Computability.VPVNP.RankQueryStackEngineSpec
import OAI.Computability.VPVNP.RAMTapeUnaryWordValue

/-! # Fixed finite control for the low bits of a descriptor tag

The code pops a fixed number of little-endian bits, restores them in the
opposite order, and enters the selected subroutine with its original bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.TagRouter

open RAMTape BurstRAM TapeWord

variable {K : Type}

/-- Read `n` low-order bits from a tag, restore them to the stack, and invoke the continuation
indexed by their little-endian value. -/
def select (k : K) : ℕ → (ℕ → FiniteRoutine K) → FiniteRoutine K
  | 0, next => next 0
  | n+1, next =>
    let branch (b : Bool) := select k n (fun i =>
      (FiniteRoutine.ofRoutine (Routine.push k b)).followedBy (next (b.toNat + 2*i)))
    .ofRoutine (Routine.popCase k (Routine.halt false) (branch false).body (branch true).body)

variable [DecidableEq K]

theorem select_runs (k : K) (next : ℕ → FiniteRoutine K) (bits tail : List Bool)
    (s out : Stacks K) (hs : s k = bits ++ tail) {t : ℕ}
    (hr : (next (value bits)).Runs t s out) :
    (select k bits.length next).Runs (2*bits.length+t) s out := by
  induction bits generalizing next s t with
  | nil => simpa only [List.length_nil, select, Nat.mul_zero, Nat.zero_add, value] using hr
  | cons b bs ih =>
    let cut := Function.update s k (bs ++ tail)
    let arm (i : ℕ) := (FiniteRoutine.ofRoutine (Routine.push k b)).followedBy (next (b.toNat+2*i))
    have hrestore : Function.update cut k (b :: cut k) = s := by
      simp only [cut, Function.update_self, Function.update_idem]
      change s k = b :: (bs ++ tail) at hs
      rw [← hs, Function.update_eq_self]
    have push := Routine.runs_push k b cut
    rw [hrestore] at push
    have armrun : (arm (value bs)).Runs (1+t) cut out := push.followedBy hr
    have recur := ih arm cut (Function.update_self ..) armrun
    rw [List.length_cons, show 2*(bs.length+1)+t = 2*bs.length+(1+t)+1 by omega]
    cases b with
    | false => exact Routine.runs_popCase_false _ _ _ _ hs recur
    | true => exact Routine.runs_popCase_true _ _ _ _ hs recur

/-- A tag known to fit in the tested bits is selected exactly. -/
theorem digits_runs (k : K) (next : ℕ → FiniteRoutine K) {w d tag t : ℕ}
    (hd : d ≤ w) (ht : tag < 2^d) (s out : Stacks K) (hs : s k = UniversalCountStack.digits w tag)
    (hr : (next tag).Runs t s out) : (select k d next).Runs (2*d+t) s out := by
  let bits := UniversalCountStack.digits d tag
  let tail := List.replicate (w-d) false
  have hb : value bits = tag := by rw [UniversalCountStack.value_digits, Nat.mod_eq_of_lt ht]
  have htw : tag < 2^w := ht.trans_le (Nat.pow_le_pow_right (by decide) hd)
  have htail : value tail = 0 := by
    rw [show tail = wordBits (0 : Word (w-d)) from UnaryWord.zeros_wordBits _, value_wordBits]; rfl
  have he : UniversalCountStack.digits w tag = bits ++ tail := by
    apply eq_of_length_value
    · simp only [bits,tail,UniversalCountStack.length_digits,List.length_append,List.length_replicate]; omega
    · rw [UniversalCountStack.value_digits, Nat.mod_eq_of_lt htw, value_append, hb, htail, mul_zero, add_zero]
  rw [he] at hs
  have h := select_runs k next bits tail s out hs (hb ▸ hr)
  simpa only [bits,UniversalCountStack.length_digits] using h

end RankQuery.Stack.TagRouter

end VPVNP
end Computability
end OAI
