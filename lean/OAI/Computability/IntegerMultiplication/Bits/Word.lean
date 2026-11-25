import OAI.Computability.IntegerMultiplication.Code.Slice

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Big naturals as little-endian lists of bits with possible leading zeroes at the *end*. -/

namespace Bits

open Code
abbrev Word := List Bool

def digit : Bool → ℕ
  | false => 0
  | true => 1

@[simp] theorem d0 : digit false=0 := rfl
@[simp] theorem d1 : digit true=1 := rfl
@[simp] theorem digit_le (b) : digit b≤1 := by cases b <;> decide

def value : Word → ℕ
  | [] => 0
  | b::l => digit b+2*value l

@[simp] theorem value_nil : value []=0 := rfl
@[simp] theorem value_cons (b l) : value (b::l)=digit b+2*value l := rfl

private theorem carry_mod (b : Bool) (x : ℕ) : (digit b+2*x)%2=digit b := by
  have := digit_le b; omega

@[simp] theorem value_odd (b l) : value (b::l)%2=digit b := carry_mod _ _

@[simp] theorem value_half (b l) : value (b::l)/2=value l := by
  have := digit_le b; simp; omega

theorem value_lt (l : Word) : value l< 2^l.length := by
  induction l with
  | nil => decide
  | cons b l ih =>
    rw [List.length_cons,value_cons,pow_succ]
    have := digit_le b
    omega

theorem value_append (l s : Word) :
    value (l++s)=value l+2^l.length*value s := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.cons_append,value_cons,ih,List.length_cons,pow_succ,Nat.mul_add]
    -- omega for products assoc via simp mul.left_comm
    rw [Nat.mul_comm (2^l.length) 2,Nat.mul_assoc]
    omega

@[simp] theorem zeroes (n) : value (List.replicate n false) = 0 := by
  induction n <;> simp_all [List.replicate_succ]

def resize (i : Tally × Word) : Word :=
  cutLists (i.1, i.2 ++ fill false i.1) |>.1

@[fun_prop] theorem easy_resize {X : Type*} [Codec X] {f : X → Tally × Word} (h : Easy f) :
    Easy (fun x => resize (f x)) := by
  apply (easy_cut (X := Bool) (g := fun x => ((f x).1,(f x).2 ++ fill false (f x).1)) ?_).compose Easy.fst
  fun_prop

def sized (n : ℕ) (l : Word) : Word := resize (tally n,l)

@[simp] theorem sized_length (n l) : (sized n l).length=n := by
  simp [sized,resize,cutLists,fill,tally_length]

theorem sized_eq (n l) : sized n l = (l ++ List.replicate n false).take n := by
  simp [sized,resize,cutLists,tally,fill]

theorem sized_low (n l) :
    value (sized n l) = value l % 2^n := by
  rw [sized_eq]
  let p := l ++ List.replicate n false
  change value (p.take n)=_
  have hl : (p.take n).length=n := by rw [← sized_eq, sized_length]
  have hv := value_append (p.take n) (p.drop n)
  rw [List.take_append_drop,show value p=value l by simp [p,value_append],hl] at hv
  rw [hv,Nat.add_mul_mod_self_left]
  have he := value_lt (p.take n)
  rw [hl] at he
  exact (Nat.mod_eq_of_lt he).symm

theorem word_inject (l s : Word) (h : l.length=s.length) (e : value l=value s) : l=s := by
  induction l generalizing s with
  | nil => cases s <;> simp_all
  | cons x l ih =>
    cases s with
    | nil => simp at h
    | cons b s =>
      have hb : x=b := by
        have h := congrArg (·%2) e
        simp only [value_odd] at h
        cases x <;> cases b <;> simp_all
      subst x
      have ht := congrArg (·/2) e
      simp only [value_half] at ht
      apply congrArg (_ :: ·)
      apply ih _ _ ht
      simpa using h

theorem size_word (l : Word) : Code.size l=2*l.length+1 := by
  induction l <;> simp_all; omega

/-- Canonical spelling n to exactly m bits. -/
def phrase (m n : ℕ) : Word :=
  match m with
  | 0 => []
  | k+1 => (if n%2=0 then false else true)::phrase k (n/2)

theorem phrase_length (m n) : (phrase m n).length=m := by
  induction m generalizing n <;> simp_all [phrase]

private theorem digit_phrase (n : ℕ) : digit (if n%2=0 then false else true) = n%2 := by
  split
  · simp_all
  · next h => simp; omega

theorem value_phrase {m n} (h : n<2^m) : value (phrase m n)=n := by
  induction m generalizing n with
  | zero => simp at h; simp [phrase,h]
  | succ m ih =>
    rw [phrase,value_cons,digit_phrase,ih]
    · omega
    rw [pow_succ] at h
    omega

/-- more general canonical form can use the % version by supplying the reduced n. -/
def short (m n : ℕ) : Word := phrase m (n % 2^m)

@[simp] theorem value_short (m n : ℕ) : value (short m n)=n%2^m :=
  value_phrase (Nat.mod_lt _ (Nat.pow_pos (by decide)))

@[simp] theorem short_length (m n : ℕ) : (short m n).length=m := phrase_length _ _

end Bits

end IntegerMultiplication
end Computability
end OAI
