import OAI.Computability.VPVNP.RankQueryTagRouter
import OAI.Computability.VPVNP.RankQueryGramReadSpace

/-! # Tag dispatch reuses the selected branch's live storage -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.TagRouter

open RAMTape BurstRAM TapeWord UniversalCountStack

variable {K : Type} [DecidableEq K]

private theorem pop_bounded (k : K) (low high : FiniteRoutine K) (b : Bool) (tail : List Bool)
    {cap t : ℕ} {s out : Stacks K} (start : ∀ a, (s a).length ≤ cap) (hs : s k = b :: tail)
    (run : (if b then high else low).BoundedRun cap t (Function.update s k tail) out) :
    (FiniteRoutine.ofRoutine (Routine.popCase k (Routine.halt false) low.body high.body)).BoundedRun cap (t+1) s out := by
  let r := Routine.popCase k (Routine.halt false) low.body high.body
  cases b with
  | false =>
    change low.BoundedRun cap t (Function.update s k tail) out at run
    have h := run.linkRoutine r (Sum.inr ∘ Sum.inr ∘ Sum.inl) none (fun _ => rfl)
    apply SpaceRun.cons start _ h
    change StackStep r.standalone (some r.entry) s (some (.inr (.inr (.inl low.body.entry)))) (Function.update s k tail)
    simpa only [hs,List.head?_cons,List.tail_cons] using
      (StackStep.pop (code := r.standalone) (s := s) (q := some r.entry) (show r.standalone (some r.entry) = .pop k _ from rfl))
  | true =>
    change high.BoundedRun cap t (Function.update s k tail) out at run
    have h := run.linkRoutine r (Sum.inr ∘ Sum.inr ∘ Sum.inr) none (fun _ => rfl)
    apply SpaceRun.cons start _ h
    change StackStep r.standalone (some r.entry) s (some (.inr (.inr (.inr high.body.entry)))) (Function.update s k tail)
    simpa only [hs,List.head?_cons,List.tail_cons] using
      (StackStep.pop (code := r.standalone) (s := s) (q := some r.entry) (show r.standalone (some r.entry) = .pop k _ from rfl))

theorem select_bounded (k : K) (next : ℕ → FiniteRoutine K) (bits tail : List Bool)
    {cap t : ℕ} (s out : Stacks K) (hs : s k = bits ++ tail) (hr : (next (value bits)).BoundedRun cap t s out) :
    (select k bits.length next).BoundedRun cap (2*bits.length+t) s out := by
  induction bits generalizing next s t with
  | nil => simpa only [List.length_nil,select,Nat.mul_zero,Nat.zero_add,value] using hr
  | cons b bs ih =>
    let cut := Function.update s k (bs ++ tail)
    let arm (i : ℕ) := (FiniteRoutine.ofRoutine (Routine.push k b)).followedBy (next (b.toNat+2*i))
    change s k = b :: (bs ++ tail) at hs
    have restore : Function.update cut k (b :: cut k) = s := by
      simp only [cut,Function.update_self,Function.update_idem]; rw [← hs,Function.update_eq_self]
    have start := hr.initial_cap
    have hcut (i : K) : (cut i).length ≤ cap := by
      by_cases hi : i = k
      · subst i; have hk := start k; rw [hs,List.length_cons] at hk
        rw [show cut k = _ from Function.update_self ..]; omega
      · simpa [cut,hi] using start i
    have push : (FiniteRoutine.ofRoutine (Routine.push k b)).BoundedRun cap 1 cut s := by
      rw [← restore]
      exact .cons hcut (.push rfl) (.nil _ _ (restore ▸ start))
    have armrun : (arm (value bs)).BoundedRun cap (1+t) cut out := push.followedBy hr
    have recur := ih arm cut (Function.update_self ..) armrun
    rw [List.length_cons,show 2*(bs.length+1)+t = 2*bs.length+(1+t)+1 by omega]
    cases b with
    | false => exact pop_bounded _ _ _ false _ start hs recur
    | true => exact pop_bounded _ _ _ true _ start hs recur

theorem digits_bounded (k : K) (next : ℕ → FiniteRoutine K) {w d tag cap t : ℕ}
    (hd : d ≤ w) (ht : tag < 2^d) (s out : Stacks K) (hs : s k = UniversalCountStack.digits w tag)
    (hr : (next tag).BoundedRun cap t s out) : (select k d next).BoundedRun cap (2*d+t) s out := by
  let bits := UniversalCountStack.digits d tag
  let tail := List.replicate (w-d) false
  have hb : value bits = tag := by rw [UniversalCountStack.value_digits, Nat.mod_eq_of_lt ht]
  have htw : tag < 2^w := ht.trans_le (Nat.pow_le_pow_right (by decide) hd)
  have htail : value tail = 0 := by
    rw [show tail = wordBits (0 : Word (w-d)) from UnaryWord.zeros_wordBits _, value_wordBits]; rfl
  have he : UniversalCountStack.digits w tag = bits ++ tail := by
    apply eq_of_length_value
    · simp only [bits,tail,UniversalCountStack.length_digits,List.length_append,List.length_replicate]; omega
    · rw [UniversalCountStack.value_digits,Nat.mod_eq_of_lt htw,value_append,hb,htail,mul_zero,add_zero]
  rw [he] at hs
  have h := select_bounded k next bits tail s out hs (hb ▸ hr)
  simpa only [bits,UniversalCountStack.length_digits] using h

end RankQuery.Stack.TagRouter

end VPVNP
end Computability
end OAI
