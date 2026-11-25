import OAI.Computability.IntegerMultiplication.Bits.Add
import Mathlib

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Dusk
open Code Bits
-- word width k+1, retain canonical. modulus one allowed.
def period (k : ℕ) := 2^(k+1)-1
theorem period_s (k : ℕ) : period k+1=2^(k+1) := by
  rw [period]
  have : 1≤2^(k+1) := Nat.one_le_pow _ _ (by decide)
  omega
theorem certain (k : ℕ) : 0<period k := by
  have := period_s k
  rw [pow_succ] at this
  have : 1≤2^k := Nat.one_le_pow _ _ (by decide)
  omega
abbrev day (k : ℕ) := ZMod (period k)
instance (k : ℕ) : NeZero (period k) := ⟨(certain _).ne'⟩
def trip {k : ℕ} (x : day k) := phrase (k+1) x.val
@[simp] theorem trip_length {k} (x : day k) : (trip x).length=k+1 := phrase_length _ _
@[simp] theorem trips {k} (x : day k) : Bits.value (trip x)=x.val := by
  have e := ZMod.val_lt x
  have z := period_s k
  exact value_phrase (by omega)

-- reduce a Word up to 2*period, once. compute lengths from gauge ruler supplied.
def era (j : Tally) : Word := fill true j
theorem point (s : Tally) : (era s).length=s.length := by simp [era,fill]
theorem peak (w : Tally) : Bits.value (era w)+1=2^w.length := by
  have h (n : ℕ) : Bits.value (List.replicate n true)+1=2^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.replicate_succ,value_cons, ← d1.symm,pow_succ]
      omega
  rw [era,fill_eq,h]

def plan (m : Tally × Word) : Word :=
  let y := Bits.sub (m.2,era m.1)
  resize (m.1,bif y.2 then m.2 else y.1)
theorem planned : Easy plan := by
  let g := fun m : Tally × Word => Bits.sub (m.2,era m.1)
  have h₁ : Easy (era) := easy_fill true (easy_id)
  have h₂ : Easy g := by unfold g; fun_prop
  have e := (h₂.sndCompose.pair (h₂.fstCompose.pair (Easy.snd (X:=Tally) (Y:=Word)))).compose
    (Easy.ifst Easy.fst Easy.snd)
  exact easy_resize (Easy.fst.pair e)

theorem plan_lt {w : Tally} {k} (t : w.length=k+1)
    (x : Word) (z : Bits.value x < 2*period k) :
    plan (w,x)=trip ((Bits.value x:day k)) := by
  have q : Bits.value (era w)=period k := by
    have := peak w
    have := period_s k
    rw [t] at *; omega
  let v := era w
  let i := Bits.sub (x,v)
  change Bits.resize (w,bif i.2 then x else i.1)=_
  rw [show w=tally (k+1) from by
      calc w = List.replicate w.length () := List.eq_replicate_length.mpr (by simp)
           _ = tally (k+1) := by rw [t]; rfl]
  apply Bits.word_inject
  · exact (sized_length ..).trans (trip_length _).symm
  change Bits.value (sized (k+1) _) = _
  rw [sized_low,trips,ZMod.val_natCast]
  have e := period_s k
  by_cases a : Bits.value x < period k
  · rw [show i.2=true from (sub_borrow x v).mpr (by simpa [v,q])]
    simp only [Bool.cond_true]
    exact (Nat.mod_eq_of_lt (by omega)).trans (Nat.mod_eq_of_lt a).symm
  have b : i.2=false := by
    have h : i.2≠true := fun m => a (by simpa [v,q] using (sub_borrow x v).mp m)
    cases g : i.2 <;> simp_all
  rw [b]
  change Bits.value (sub (x,v)).1 % _=_
  rw [sub_val_le x v (by simp [v,q,le_of_not_gt a]),q]
  have g : Bits.value x % period k = Bits.value x-period k := by
    have := certain k
    -- omega nonlin modulo variable period. use mod via sub
    exact (Nat.mod_eq_sub_mod (by omega)).trans (Nat.mod_eq_of_lt (by omega))
  rw [g,Nat.mod_eq_of_lt (by omega)]

def mug (x : Word × Word) := plan (ruler x.1,Bits.add x)
def shade (x : Word) := plan (ruler x,(Bits.sub (era (ruler x),x)).1)
theorem mug_easy : Easy mug := by
  apply (Easy.pair (Easy.ruler Easy.fst) (easy_add (easy_id (X:=Word×Word)))).compose planned
theorem shade_easy : Easy shade := by
  have e : Easy era := easy_fill true easy_id
  exact (show Easy (fun x : Word => (ruler x,(Bits.sub (era (ruler x),x)).1)) from by fun_prop).compose planned
theorem mugged {k} (x y : day k) :
    mug (trip x,trip y) = trip (x+y) := by
  have v : Bits.value (Bits.add (trip x,trip y))=x.val+y.val := by simp [add_val]
  have z := ZMod.val_lt x; have j := ZMod.val_lt y
  unfold mug
  have hr : (ruler (trip x)).length = k+1 := by simp
  rw [plan_lt hr _ (by rw [v]; omega),v,Nat.cast_add,
    ZMod.natCast_val,ZMod.natCast_val]
  simp
theorem shaded {k} (x : day k) :
    shade (trip x) = trip (-x) := by
  let w := ruler (trip x)
  have t : w.length=k+1 := by simp [w]
  have q : Bits.value (era w)=period k := by have := peak w; have := period_s k; rw [t] at *; omega
  have z := ZMod.val_lt x
  let y := (Bits.sub (era w,trip x)).1
  have e : Bits.value y=period k-x.val := by
    unfold y -- ?
    rw [sub_val_le _ _ (by rw [q,trips]; omega),q,trips]
  change plan (w,y)=_
  rw [plan_lt t _ (by rw [e]; omega)]
  congr
  rw [e,Nat.cast_sub z.le,ZMod.natCast_self, ZMod.natCast_val,zero_sub]
  rw [ZMod.cast_id]
end Dusk

end IntegerMultiplication
end Computability
end OAI
