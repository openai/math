import OAI.Computability.IntegerMultiplication.Bits.Multiply
import OAI.Computability.IntegerMultiplication.Code.Train
import OAI.Computability.IntegerMultiplication.Code.Iter

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Grid
open Code Bits Iter
-- allow negative zero.
abbrev Sign := Bool
abbrev S := Sign × Word
def tag (s : Sign) : ℤ := bif s then -1 else 1
def whole (s : S) : ℤ := tag s.1 * value s.2
abbrev dept (s : S) := s.2.length
theorem sign_area (x:S) : Code.size x=2*dept x+3 := by rw [size_prod,show size x.1=1 from rfl,size_word,dept]; omega
theorem tag_v (s : Sign) : |tag s|=1 := by cases s <;> simp [tag]

theorem abs_whole (s : S) : |whole s|=(value s.2:ℤ) := by unfold whole; rw [abs_mul,tag_v]; simp
theorem normal (s : S) : (whole s).natAbs = value s.2 := by
  exact_mod_cast (show ((whole s).natAbs : ℤ) = (value s.2 : ℤ) from (Int.natCast_natAbs ..).trans (abs_whole s))
theorem zone (s : S) : |whole s| < 2^dept s := by rw [abs_whole]; exact_mod_cast value_lt _
abbrev Zeros (s:S) := s.2.reverse.headD false
def neg (x : S) : S := (!x.1,x.2)
@[fun_prop] theorem easy_neg : Easy neg := by unfold neg; fun_prop
theorem neg_r (x : S) : whole (neg x) = -whole x := by
  rcases x with ⟨b,w⟩; cases b <;> simp [whole,neg,tag]

-- generic ternary solver
theorem easy_bool {X Y} [Codec X] [Codec Y] (f : X→ Sign) (a b : X→ Y)
    (h : Easy f) (v:Easy a) (q : Easy b) :
    Easy fun x=> bif f x then a x else b x :=
  (h.pair (v.pair q)).compose (Easy.ifst Easy.snd Easy.fst)

def takePlus (a : S×S) : S :=
  (a.1.1, Bits.add (a.1.2,a.2.2))
def takeSub (x : S × S) : S :=
  (x.1.1,(Bits.sub (x.1.2,x.2.2)).1)
def borrow (x:S×S) := more (x.2.2,x.1.2)
def minusMax (x:S×S) :=
    bif borrow x then takeSub x.swap else takeSub x
def plus (x:S×S) :=
  bif decide (x.1.1=x.2.1) then takePlus x else minusMax x

@[fun_prop] theorem easy_plus : Easy plus := by
  have d : Easy takePlus := by unfold takePlus; fun_prop
  have m : Easy takeSub := by unfold takeSub; fun_prop
  have x : Easy borrow := by unfold borrow; fun_prop
  have y : Easy minusMax := easy_bool _ _ _ x (Easy.exchange.compose m) m
  exact easy_bool _ _ _ (Easy.compose (show Easy (fun i:S×S=> (i.1.1,i.2.1)) from by fun_prop)
    (Easy.finite (fun i:Sign×Sign => decide (i.1=i.2)))) d y
theorem plus_v (p q : S) :
    whole (plus (p,q))=whole p+whole q := by
  unfold plus minusMax
  dsimp only
  by_cases h : p.1=q.1
  · simp [h,whole,takePlus,Bits.add_val,mul_add]
  have e : tag p.1= -tag q.1 := by
    cases w:p.1 <;> cases v:q.1 <;> simp_all [tag]
  simp only [h,decide_false, Bool.cond_false]
  by_cases g : borrow (p,q)=true
  ·
    have k : value p.2 < value q.2 := (more_lt ..).1 g
    rw [g]; unfold takeSub whole
    change tag q.1*(value (Bits.sub (q.2,p.2)).1:ℕ)=_
    rw [Bits.sub_val_le q.2 p.2 k.le]
    rw [Nat.cast_sub k.le,e]; ring
  · have u : value q.2 ≤ value p.2 := Nat.le_of_not_gt (fun e=> g ((more_lt ..).2 e))
    rw [Bool.eq_false_iff.mpr g]
    change tag p.1* (Bits.value (Bits.sub (p.2,q.2)).1:ℕ) = _
    rw [Bits.sub_val_le p.2 q.2 u,Nat.cast_sub u,e,whole,whole,e]; ring

def truncate0 (x:Tally × S) : S :=
  (x.2.1, Bits.resize (x.1,x.2.2))
@[fun_prop] theorem easy_t : Easy truncate0 := by unfold truncate0; fun_prop
@[simp] theorem t_len (n : ℕ) (s:S) : dept (truncate0 (tally n,s))=n := sized_length ..
theorem t_small (n : ℕ) (s : S) (e : (whole s).natAbs < 2^n) :
    whole (truncate0 (tally n,s))=whole s := by
  rw [normal] at e
  unfold whole; change tag s.1 * (Bits.value (Bits.sized n _):ℕ)=_
  rw [sized_low,Nat.mod_eq_of_lt e]

def divpow (x : Tally × S) : S :=
  (x.2.1,(cutLists (x.1,x.2.2)).2)
@[fun_prop] theorem easy_divpow : Easy divpow := Easy.snd.fstCompose.pair ((easy_cut (g:=fun x:Tally×S=>(x.1,x.2.2)) (Easy.fst.pair Easy.snd.sndCompose)).sndCompose)
def slash (n:ℕ) (x : ℤ) := x.sign * (x.natAbs / 2^n : ℕ)

private theorem shift_ (l : Word) (s) :
    value (l.drop s) = value l / 2^s := by
  induction s generalizing l with
  | zero => simp
  | succ s ih =>
    cases l with
    | nil=>simp
    | cons a v =>
      change value (v.drop s)=_
      simp only [pow_succ',← Nat.div_div_eq_div_mul,value_half,ih]

private theorem signal (k:ℤ) (t u:ℕ) (d : |k|=1) (h : u ≤ t) :
    k* (u:ℕ) = (k*t).sign * (u:ℕ) := by
  cases lt_or_ge 0 t with
  | inl y =>
    have v : (0:ℤ) < ↑t := by exact_mod_cast y
    rcases eq_or_eq_neg_of_abs_eq d with q|q
    · rw [q,one_mul,one_mul,Int.sign_eq_one_of_pos v,one_mul]
    · simp only [q,neg_mul,one_mul]; rw [Int.sign_eq_neg_one_of_neg (neg_lt_zero.mpr v),neg_mul,one_mul]
  | inr e=> rw [show u=0 from (by omega)]; simp

theorem divpow_v (n) (x : S):
    whole (divpow (tally n,x))=slash n (whole x) := by
  unfold slash; rw [normal]
  unfold whole; unfold divpow
  dsimp only
  unfold cutLists; dsimp only
  rw [tally_length,shift_,signal _ (value x.2) _ (tag_v _) (Nat.div_le_self ..)]

end Grid

end IntegerMultiplication
end Computability
end OAI
