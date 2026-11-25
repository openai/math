import OAI.Computability.IntegerMultiplication.Bits.Add

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Bits

open Code

def more (i : Word × Word) : Bool := (sub (i.2,i.1)).2

@[fun_prop]
theorem easy_more {X : Type*} [Codec X] {f : X → Word × Word} (h : Easy f) :
    Easy (fun x => more (f x)) := by
  apply (easy_sub (f := fun i => ((f i).2,(f i).1)) ?_).sndCompose
  fun_prop

theorem more_lt (i j : Word) : more (i,j)=true ↔ value j<value i :=
  sub_borrow j i

def shift (i : Tally × Word) := fill false i.1 ++ i.2

@[fun_prop]
theorem easy_shift {X : Type*} [Codec X] {f : X → Tally × Word} (h : Easy f) :
    Easy (fun x => shift (f x)) := by unfold shift; fun_prop

@[simp]
theorem shift_value (i z) :
    value (shift (i,z)) = 2^i.length*value z := by simp [shift, fill_eq,value_append]

/-- multiplication by a fixed natural. large constant acceptable. -/
def scale (n : ℕ) (w : Word) : Word :=
  match n with
  | 0 => []
  | k+1 => add (w,scale k w)

theorem scale_exact (k w) : value (scale k w)=k*value w := by
  induction k with
  | zero => simp [scale]
  | succ k ih => rw [scale,add_val,ih,Nat.add_mul]; simp [add_comm]

-- don't add to fun_prop? has param n treated main? define with n fixed by comp
@[fun_prop]
theorem easy_scale {X : Type*} (k : ℕ) [Codec X] {f : X→Word} (h : Easy f) :
    Easy (fun x => scale k (f x)) := by
  induction k <;> unfold scale
  · exact Easy.const _
  fun_prop

variable {p : ℕ}

instance finCodec : Codec (Fin p) :=
  ⟨fun x => send (tally x.val)⟩

instance : FiniteState (Fin p) where
  identify a b h := by
    apply Fin.ext
    have e := congrArg Tree.count h
    change size (tally a.val) = size (tally b.val) at e
    rw [size_tally,size_tally,tally_length,tally_length] at e
    omega

private def nextnum (k : Fin p) (b : Bool) : ℕ := 2*k.val+digit b

private theorem next_bound (k : Fin p) (b : Bool) :
    nextnum k b < p+p := by unfold nextnum; have := k.isLt; have := digit_le b; omega

/-- One step of MSB-first quotient by fixed positive p. -/
private def divide (b : Bool) (k : Fin p) : Fin p × List Bool :=
  (⟨if p ≤ nextnum k b then nextnum k b-p else nextnum k b, by
    split
    · have := next_bound k b; omega
    · omega⟩,
   [decide (p ≤ nextnum k b)])

private theorem divide_one (b : Bool) (k : Fin p) :
    ∃ x d, divide b k = (x,[d]) ∧ 2*k.val+digit b=p*digit d+x.val := by
  refine ⟨_,_,rfl,?_⟩
  by_cases h : p≤nextnum k b
  · simp only [h, decide_true,↓reduceIte,d1,mul_one]
    change 2*k.val+digit b = p+(2*k.val+digit b-p)
    exact (Nat.add_sub_of_le h).symm
  · simp only [ite_eq_right h, decide_eq_false h,d0, Nat.mul_zero,Nat.zero_add]
    rfl

-- number of a big-endian word
def backvalue (l : Word) : ℕ := value l.reverse

private theorem back_cons (b : Bool) (l : Word) :
    backvalue (b::l)=backvalue l+2^l.length*digit b := by
  simp [backvalue,value_append]

private theorem divide_list (l : Word) (k : Fin p) :
    let i := machine divide (l,k)
    i.1.length=l.length ∧
    2^l.length*k.val+backvalue l=p*backvalue i.1+i.2.val := by
  dsimp only
  induction l generalizing k with
  | nil => simp [machine_nil,backvalue]
  | cons b l ih =>
    obtain ⟨a,d,h,e⟩ := divide_one b k
    obtain ⟨o,k',hh⟩ : ∃ o k', machine divide (l,a)=(o,k') := ⟨_,_,rfl⟩
    specialize ih a
    simp only [machine_cons,h,hh,List.cons_append,List.nil_append,List.length_cons,back_cons,pow_succ]
    rw [hh] at ih
    dsimp only at ih
    rw [ih.1,Nat.mul_add,Nat.mul_assoc]
    have heq := congrArg (fun x => 2^l.length*x) e
    simp only [Nat.mul_add] at heq
    rw [Nat.mul_left_comm p] -- try
    constructor
    · rfl
    omega

/-- only for fixed p (the finite control compiles its table); expose quotient with
exactly the length of l. -/
def qword [NeZero p] (l : Word) : Word :=
  (machine divide (l.reverse,(0 : Fin p))).1.reverse

-- need p explicit, Lean def p implicit doesn't occur? qword (p:=p).
@[fun_prop]
theorem easy_qword {X : Type*} [NeZero p] [Codec X] {f : X → Word} (h : Easy f) :
    Easy (fun x => qword (p:=p) (f x)) := by
  let g := fun x => machine divide ((f x).reverse,(0 : Fin p))
  have hg : Easy g := by
    apply Easy.machine
    fun_prop
  change Easy (fun x => (g x).1.reverse)
  fun_prop

theorem qword_length [NeZero p] (l : Word) : (qword (p:=p) l).length=l.length := by
  unfold qword
  simpa using (divide_list l.reverse (0 : Fin p)).1

theorem qword_value [NeZero p] (l : Word) : value (qword (p:=p) l)=value l/p := by
  unfold qword
  change backvalue _=_
  have he := (divide_list l.reverse (0 : Fin p)).2
  rw [Fin.val_zero,Nat.mul_zero,Nat.zero_add,show backvalue l.reverse=value l by simp [backvalue]] at he
  rw [he,Nat.add_comm (p*_),Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (NeZero.ne p)),
    Nat.div_eq_of_lt _]
  · simp
  · exact Fin.isLt _

end Bits

end IntegerMultiplication
end Computability
end OAI
