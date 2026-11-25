import OAI.Computability.IntegerMultiplication.Toom.Model
import OAI.Computability.IntegerMultiplication.Bits.Small

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Toom
open Code Bits Finset
variable {K : ℕ}

/-- Counting ticks for the call width. `K` fixed in the machine. Extra K-1 ticks yield
the ceiling division needed. -/
private def tick (_ : Unit) (j : Fin K) : Fin K × List Unit :=
  if h : j.val+1<K then (⟨j.val+1,h⟩,[]) else (⟨0, by have := j.isLt; omega⟩,[()])

private theorem tick_bounds (x : Tally) (j : Fin K) :
    x.length + j.val = ((machine tick (x,j)).1.length * K + (machine tick (x,j)).2.val) := by
  induction x generalizing j with
  | nil => simp [machine_nil]
  | cons a l ih =>
    rw [machine_cons,tick]
    split_ifs with hk
    ·
      obtain ⟨v,j',he⟩ : ∃ v j', machine tick (l,(⟨j.val+1,hk⟩:Fin K))=(v,j') := ⟨_,_,rfl⟩
      specialize ih ⟨_,hk⟩
      simp [he] at ih ⊢
      omega
    ·
      have hk₀ : 0<K := by have := j.isLt; omega
      obtain ⟨v,j',he⟩ : ∃ v j', machine tick (l,(⟨0,hk₀⟩:Fin K))=(v,j') := ⟨_,_,rfl⟩
      specialize ih ⟨0,hk₀⟩
      simp [he,Nat.add_mul] at ih ⊢
      have h' := j.isLt
      omega

def piece (K : ℕ) [NeZero K] (l : Tally) : Tally :=
  (machine tick (l++tally (K-1),(0 : Fin K))).1

variable [NeZero K]

@[fun_prop]
theorem easy_piece {X : Type*} [Codec X] {f : X → Tally} (h : Easy f) :
    Easy (fun x => piece K (f x)) := by
  apply Easy.fstCompose
  apply Easy.machine
  fun_prop

theorem piece_bounds (l : Tally) :
    l.length ≤ (piece K l).length*K ∧
    (piece K l).length*K < l.length+K := by
  have h := tick_bounds (l++tally (K-1)) (0 : Fin K)
  unfold piece
  simp only [List.length_append,tally_length, Fin.val_zero,Nat.add_zero] at h
  have he := (machine tick (l++tally (K-1),(0 : Fin K))).2.isLt
  have hk := Nat.pos_of_ne_zero (NeZero.ne K)
  omega

/-- Retrieve chunk number j by repeating cutLists a *fixed* number of times. -/
def chunk (j : ℕ) (l : Tally × Word) : Word :=
  match j with
  | 0 => (cutLists l).1
  | j+1 => chunk j (l.1,(cutLists l).2)

@[fun_prop]
theorem easy_chunk {X : Type*} [Codec X] {f : X→ Tally × Word} (h : Easy f) (j) :
    Easy (fun i => chunk j (f i)) := by
  induction j generalizing X with
  | zero =>
    change Easy (fun i => (cutLists (f i)).1)
    exact (easy_cut (X:=Bool) h).fstCompose
  | succ j ih =>
    unfold chunk
    apply ih
    apply h.fstCompose.pair
    exact (easy_cut (X:=Bool) h).sndCompose

theorem chunk_length (j l) : (chunk j l).length≤ l.1.length := by
  induction j generalizing l with
  | zero => simp [chunk,cutLists]
  | succ j ih => unfold chunk; exact ih _

/-- coverage: all digits of x, possibly including shorter final or empty chunks. -/
theorem chunks {n : ℕ} {r : Tally} {x : Word} (h : x.length≤r.length*n) :
    weigh (2^r.length) (fun i : Fin n => value (chunk i.val (r,x))) = value x := by
  induction n generalizing x with
  | zero =>
    have hx : x=[] := List.length_eq_zero_iff.mp (by simpa using h)
    simp [hx,weigh]
  | succ n ih =>
    rw [weigh, Fin.sum_univ_succ]
    let y := (cutLists (r,x)).2
    have he (i : Fin n) :
        value (chunk i.succ.val (r,x)) * (2^r.length)^(i.succ.val) =
        value (chunk i.val (r,y)) * (2^r.length)^i.val * 2^r.length := by
      change value (chunk (i.val+1) (r,x))*_^ (i.val+1)=_
      rw [chunk,pow_succ,← Nat.mul_assoc]
    simp_rw [he, ← sum_mul, show (0 : Fin (n+1)).val=0 from rfl]
    change _ + weigh (2^r.length) (fun i : Fin n => value (chunk i.val (r,y)))* _ = _
    rw [ih, chunk,Nat.pow_zero,mul_one]
    · have hq := value_append (x.take r.length) (x.drop r.length)
      by_cases e : r.length≤x.length
      · rw [List.take_append_drop,List.length_take, Nat.min_eq_left e] at hq
        exact (by rw [Nat.mul_comm (2^r.length)] at hq; exact hq.symm)
      · have hh := (show x.length≤r.length by omega)
        simp [y,cutLists, List.take_of_length_le hh, List.drop_eq_nil_of_le hh]
    · rw [Nat.mul_succ] at h
      simp [y,cutLists]
      omega

def sumbits (l : List Word) := l.foldr (fun x y => add (x,y)) []

@[simp] theorem sumval (l : List Word) :
    value (sumbits l)=(l.map value).sum := by
  induction l <;> simp_all [sumbits,add_val]

/-- run finite matrix/list. use List.ofFn to connect with weigh/recover identities. -/
theorem easy_ofFn {X Z : Type*} [Codec X] [Codec Z] {n : ℕ} (l : Fin n → X → Z) (h : ∀ i, Easy (l i)) :
    Easy (fun x : X => List.ofFn (fun i : Fin n => l i x)) := by
  induction n with
  | zero => simpa using (Easy.const ([] : List Z) : Easy (fun (_:X) => []))
  | succ n ih =>
    simp_rw [List.ofFn_succ]
    have htail := ih (fun i => l i.succ) (fun i => h _)
    have h := h 0
    exact (h.pair htail).compose Easy.cons

theorem easy_big_sum {X : Type*} [Codec X] {n : ℕ} (l : Fin n → X → Word) (h : ∀ i, Easy (l i)) :
    Easy (fun x : X => sumbits (List.ofFn (fun i => l i x))) := by
  induction n with
  | zero => exact Easy.const _
  | succ n ih =>
    simp only [List.ofFn_succ,sumbits,List.foldr_cons]
    have htail := ih (fun i => l i.succ) (fun i => h _)
    have h := h 0
    apply easy_add
    exact h.pair htail

def eval (n x : ℕ) (i : Tally × Word) :=
  sumbits (List.ofFn (fun j : Fin n => scale (x^j.val) (chunk j.val i)))

@[fun_prop] theorem easy_eval (n x : ℕ) {X : Type*} [Codec X] {f : X → Tally × Word} (h : Easy f) :
    Easy (fun i => eval n x (f i)) :=
  h.compose <| easy_big_sum _ (fun _ => easy_scale _ (easy_chunk (Easy.identity) _))

theorem eval_eq (n x) (r : Tally) (w : Word) :
    value (eval n x (r,w)) = weigh x (fun i : Fin n => value (chunk i.val (r,w))) := by
  unfold eval weigh
  rw [sumval, List.map_ofFn, List.sum_ofFn]
  apply sum_congr rfl
  intro i _
  change value (scale ..) = _
  rw [scale_exact,Nat.mul_comm]

def allowance (n : ℕ) := ∑ i : Fin n, (2*n)^i.val

theorem eval_small (n : ℕ) (x) (r : Tally) (w : Word) (h : x<2*n) :
    value (eval n x (r,w)) < 2^(r.length+allowance n) := by
  rw [eval_eq,weigh]
  have he (i : Fin n) :
      value (chunk i.val (r,w)) * x^i.val ≤ (2*n)^i.val * 2^r.length := by
    rw [Nat.mul_comm]
    apply Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) i.val)
    calc
      _ ≤ 2^(chunk i.val (r,w)).length := (value_lt _).le
      _ ≤ 2^r.length := pow_le_pow_right₀ (by norm_num) (chunk_length i.val (r,w))
  apply lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => he i))
  rw [← sum_mul,Nat.pow_add,Nat.mul_comm (2^r.length)]
  exact Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self (n := allowance n)) (Nat.pow_pos (by decide))

-- m+allowance exact cropped representation.
def tiny (n x : ℕ) (i : Tally × Word) : Word :=
  resize (i.1 ++ tally (allowance n), eval n x i)

@[fun_prop] theorem easy_tiny (n x : ℕ) {X : Type*} [Codec X] {f : X → Tally × Word} (h : Easy f) :
    Easy (fun i => tiny n x (f i)) := by
  apply easy_resize
  apply Easy.pair
  · fun_prop
  exact easy_eval _ _ h

theorem tiny_exact {n x : ℕ} (hx : x<2*n) (r : Tally) (w : Word) :
    value (tiny n x (r,w)) = weigh x (fun i : Fin n => value (chunk i.val (r,w))) := by
  have h (r : Tally) : r=tally r.length := by
    induction r with
    | nil => rfl
    | cons x l ih =>
      rw [List.length_cons,tally_succ]
      cases x
      exact congrArg (() :: ·) ih
  have hh := h (r++tally (allowance n))
  rw [List.length_append,tally_length] at hh
  unfold tiny
  simp only
  rw [hh,← sized,sized_low,Nat.mod_eq_of_lt (eval_small _ _ _ _ hx),eval_eq]

theorem tiny_length (n x : ℕ) (r : Tally) (w : Word) :
    (tiny n x (r,w)).length = r.length+allowance n := by simp [tiny,resize,cutLists,fill]

end Toom

end IntegerMultiplication
end Computability
end OAI
