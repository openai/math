import OAI.Computability.IntegerMultiplication.Grid.Tax
import OAI.Computability.IntegerMultiplication.Dusk.Trail

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Grid
open Code Bits Dusk
def insert (x : S) :=
  let z := plan (ruler x.2,x.2)
  bif x.1 then shade z else z
@[fun_prop] theorem facile_ins : Easy insert := by
  have y := ((Easy.ruler Easy.snd).pair (Easy.snd (X:=Bool) (Y:=Word))).compose planned
  unfold insert; dsimp only
  exact easy_bool _ _ _ Easy.fst (y.compose shade_easy) y
variable {k:ℕ}
-- represent signs as Mersenne: valid dept k+1 (including magnitude=2^(k+1)-1) if strictly period via h; else still holds reduce subtract once.
theorem towards (x : S) (h : dept x=k+1) :
    insert x=trip (k:=k) (whole x) := by
  rcases x with ⟨b,w⟩
  have t : w.length=k+1 := h
  cases b <;>
    simp only [insert,Bool.cond_true,Bool.cond_false] <;>
    rw [plan_lt (show (ruler w).length=k+1 by simp [t])]
  any_goals simp only [Bool.cond_true,Bool.cond_false,whole,tag,neg_mul,one_mul,Int.cast_natCast,Int.cast_neg,
    Dusk.shaded]
  all_goals
    have v := value_lt w; have := Dusk.certain k; have := Dusk.period_s k; rw [t] at v; omega

-- centered interval [-(2^k-1),2^k-1] exactly unique representative. prove through sign unpack and mod
def pull (w : Word) : S :=
  bif w.reverse.headD false then (true,shade w) else (false,w)
@[fun_prop]
theorem facile_pull : Easy pull := by
  refine easy_bool _ _ _ (Easy.reverse.compose (Iter.leader false)) ((Easy.const _).pair shade_easy) ((Easy.const _).pair Easy.identity)
private theorem top (w : Word) (h : w.length=k+1) :
    w.reverse.headD false=true ↔ 2^k ≤ value w := by
  rcases List.eq_nil_or_concat w with i|⟨v,b,f⟩
  · simp [i] at h
  · rw [List.concat_eq_append] at f
    subst w
    have t : v.length=k := by simpa using h
    have u := value_lt v; rw [t] at u
    simp [value_append,t]
    cases b <;> simp; omega

def lift (x : day k) : ℤ :=
  if x.val < 2^k then x.val else -((Dusk.period k - x.val:ℕ):ℤ)
private theorem mile {z : day k} (h: 0<z.val) :
    (-z).val=period k-z.val := by
  have e : (-z:day k)= ↑(Dusk.period k - z.val : ℕ) := by
    rw [Nat.cast_sub (ZMod.val_lt z).le,ZMod.natCast_val,ZMod.cast_id,ZMod.natCast_self,zero_sub]
  have t : Dusk.period k-z.val < Dusk.period k := Nat.sub_lt (Dusk.certain _) h
  rw [e,ZMod.val_natCast,Nat.mod_eq_of_lt t]
theorem lifted (x:day k) :
    whole (pull (trip x))=lift x := by
  unfold pull
  by_cases e : (trip x).reverse.headD false=true
  · have t := (top _ (trip_length x)).1 e
    unfold lift; rw [trips] at t; rw [e,ite_eq_right (by omega)]
    simp only [Bool.cond_true, whole,tag,neg_one_mul, shaded,trips]
    rw [mile (show 0 < x.val from lt_of_lt_of_le (Nat.pow_pos (by decide)) t)]
  · rw [Bool.eq_false_iff.mpr e]
    have t : x.val< 2^k := Nat.lt_of_not_ge fun t=>e ((top _ (trip_length _)).2 (by rwa [trips]))
    simp [whole,tag,lift,t]
@[simp] theorem lift_congr (x:day k): ((lift x:ℤ):day k)=x := by
  unfold lift
  split
  next => simp
  next =>
    rw [Int.cast_neg,Int.cast_natCast,Nat.cast_sub (ZMod.val_lt x).le,ZMod.natCast_self,ZMod.natCast_val,ZMod.cast_id]
    simp

theorem lift_limit (x : day k) : |lift x|< (2:ℤ)^k := by
  have q : (0:ℤ)< 2^k := pow_pos (by decide) _
  unfold lift; split
  next h =>
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast h
  next h =>
    rw [abs_neg,abs_of_nonneg (Int.natCast_nonneg _)]
    have hi : period k-x.val < 2^k := by
      have e := period_s k; rw [pow_succ] at *
      omega
    exact_mod_cast hi

theorem send_lift {t:ℤ} (d:|t|< 2^k) :
    lift (k:=k) (t:day k) = t := by
  have ts : (0:ℤ)< 2^k := pow_pos (by decide) _
  unfold lift
  have est : (Dusk.period k:ℤ)+1=2^k*2 := by norm_cast; rw [Dusk.period_s,pow_succ]
  rw [abs_lt] at d
  by_cases h:0≤ t
  · have e : ((t:day k).val:ℤ)=t := by
      rw [ZMod.val_intCast,Int.emod_eq_of_lt h (by omega)]
    rw [ite_eq_left (by exact_mod_cast (e.trans_lt d.2))]
    exact e
  have h : -(Dusk.period k:ℤ) ≤ t := by omega
  have e : ((t:day k).val:ℤ)=t+Dusk.period k := by
    rw [ZMod.val_intCast,← show (t+(period k:ℤ))%(period k:ℤ)=t%(period k:ℤ) by simp]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [ite_eq_right (by
    suffices f : (2:ℤ)^k ≤ ↑(t:day k).val by exact (not_lt.mpr (by exact_mod_cast f))
    omega), Nat.cast_sub (ZMod.val_lt _).le,e]
  omega
-- pull length always full
theorem pull_len (x:day k): dept (pull (trip x))=k+1 := by
  unfold pull
  cases (trip x).reverse.headD false <;> simp only [Bool.cond_true,Bool.cond_false,dept,trip_length,shaded]

end Grid

end IntegerMultiplication
end Computability
end OAI
