import OAI.Computability.IntegerMultiplication.Bits.Word
import OAI.Computability.IntegerMultiplication.Code.Automata

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Bits
open Code

private def plus (i : Bool × Bool) (c : Bool) : Bool × List Bool :=
  let x := digit i.1+digit i.2+digit c
  (decide (2≤x), [decide (x%2=1)])

private def minus (i : Bool × Bool) (b : Bool) : Bool × List Bool :=
  let x := digit i.1+2-digit i.2-digit b
  (decide (x<2), [decide (x%2=1)])

private theorem plus_spec (i c) :
    ∃ b d, plus i c=(d,[b]) ∧ digit b + 2*digit d = digit i.1+digit i.2+digit c := by
  rcases i with ⟨_ | _,_ | _⟩ <;> cases c <;> simp [digit,plus]

private theorem minus_spec (i c) :
    ∃ b d, minus i c=(d,[b]) ∧ digit b + digit i.2 + digit c =
        digit i.1 + 2*digit d := by
  rcases i with ⟨_ | _,_ | _⟩ <;> cases c <;> simp [digit,minus]

private theorem traverse_length (g : Bool × Bool → Bool → Bool × List Bool)
    (hg : ∀ i b, (g i b).2.length = 1) (l : List (Bool × Bool)) (c : Bool) :
    (machine g (l,c)).1.length=l.length := by
  induction l generalizing c with
  | nil => rw [machine_nil]; rfl
  | cons x l ih =>
    obtain ⟨a,u,h⟩ : ∃ a u, g x c=(a,u) := ⟨_,_,rfl⟩
    obtain ⟨v,b,q⟩ : ∃ v b, machine g (l,a)=(v,b) := ⟨_,_,rfl⟩
    specialize ih a
    have hv := hg x c
    rw [q] at ih
    try dsimp only at ih
    rw [h] at hv
    simp only [machine_cons,List.length_cons,h,q,List.length_append]
    dsimp only at ih hv
    omega

private theorem add_spec (l : List (Bool × Bool)) (c : Bool) :
    let r := machine plus (l,c)
    value (l.map Prod.fst)+value (l.map Prod.snd)+digit c =
      value r.1+2^l.length*digit r.2 := by
  dsimp only
  induction l generalizing c with
  | nil => simp [machine_nil]
  | cons x l ih =>
    obtain ⟨a,u,h,e⟩ := plus_spec x c
    obtain ⟨v,b,q⟩ : ∃ v b, machine plus (l,u)=(v,b) := ⟨_,_,rfl⟩
    specialize ih u
    rw [q] at ih
    try dsimp only at ih
    simp only [machine_cons,List.map_cons,h,q,List.length_cons,value_cons,pow_succ]
    simp only [value_cons,List.cons_append,List.nil_append]
    rw [Nat.mul_comm (2^l.length) 2, Nat.mul_assoc]
    omega

private theorem sub_spec (l : List (Bool × Bool)) (c : Bool) :
    let r := machine minus (l,c)
    value (l.map Prod.fst)+2^l.length*digit r.2 =
      value r.1+value (l.map Prod.snd)+digit c := by
  dsimp only
  induction l generalizing c with
  | nil => simp [machine_nil]
  | cons x l ih =>
    obtain ⟨a,u,h,e⟩ := minus_spec x c
    obtain ⟨v,b,q⟩ : ∃ v b, machine minus (l,u)=(v,b) := ⟨_,_,rfl⟩
    specialize ih u
    rw [q] at ih
    try dsimp only at ih
    simp only [machine_cons,List.map_cons,h,q,List.length_cons,value_cons,pow_succ,List.cons_append,List.nil_append]
    rw [Nat.mul_comm (2^l.length) 2,Nat.mul_assoc]
    omega

/-- Natural addition also providing one extra high bit. choosen width sum not max
because zip padded with both lengths. -/
def add (z : Word × Word) : Word :=
  let r := machine plus (zipSafe false false z,false)
  r.1 ++ [r.2]

def sub (z : Word × Word) : Word × Bool :=
  machine minus (zipSafe false false z,false)

private theorem zip_len (z : Word × Word) :
    (zipSafe false false z).length=z.1.length+z.2.length := by
  simp [zipSafe,add_comm]

private theorem values_zip (z : Word × Word) :
    value ((zipSafe false false z).map Prod.fst)=value z.1 ∧
    value ((zipSafe false false z).map Prod.snd)=value z.2 := by
  unfold zipSafe
  rw [List.map_fst_zip,List.map_snd_zip]
  · simp [value_append]
  all_goals simp [add_comm]

@[fun_prop] theorem easy_add {X : Type*} [Codec X] {f : X → Word × Word} (h : Easy f) :
    Easy (fun x => add (f x)) := by
  let g := fun x => machine plus (zipSafe false false (f x),false)
  have hg : Easy g := by
    apply Easy.machine
    apply Easy.pair (easy_zipSafe false false h) (Easy.const _)
  change Easy (fun x => (g x).1 ++ [(g x).2])
  fun_prop

@[fun_prop] theorem easy_sub {X : Type*} [Codec X] {f : X → Word × Word} (h : Easy f) :
    Easy (fun x => sub (f x)) :=
  Easy.machine <| Easy.pair (easy_zipSafe false false h) (Easy.const _)

@[simp] theorem add_length (i j : Word) : (add (i,j)).length=i.length+j.length+1 := by
  have h := traverse_length plus (fun i b => by simp [plus]) (zipSafe false false (i,j)) false
  simp [add,h,zip_len]

@[simp] theorem sub_length (i j : Word) : (sub (i,j)).1.length=i.length+j.length :=
  (traverse_length minus (fun i b => by simp [minus]) _ _).trans (zip_len _)

theorem add_val (i j) : value (add (i,j))=value i+value j := by
  have h := add_spec (zipSafe false false (i,j)) false
  rcases values_zip (i,j) with ⟨a,b⟩
  simp only [a,b,zip_len, d0, Nat.add_zero] at h
  unfold add
  rw [value_append,traverse_length plus (fun i b => by simp [plus]),zip_len]
  simpa using h.symm

theorem sub_val (i j) :
    value i + 2^(i.length+j.length)*digit (sub (i,j)).2 =
    value (sub (i,j)).1+value j := by
  have h := sub_spec (zipSafe false false (i,j)) false
  rcases values_zip (i,j) with ⟨a,b⟩
  simpa only [a,b,zip_len,d0,Nat.add_zero,sub] using h

theorem sub_borrow (i j : Word) :
    (sub (i,j)).2 = true ↔ value i < value j := by
  have h := sub_val i j
  have hh := value_lt (sub (i,j)).1
  rw [sub_length i j] at hh
  cases e : (sub (i,j)).2 <;> simp [e] at * <;> omega

theorem sub_val_le (i j : Word) (h : value j ≤ value i) :
    value (sub (i,j)).1=value i-value j := by
  have e := sub_val i j
  cases hb : (sub (i,j)).2
  · simp [hb] at e
    omega
  · have hh := (sub_borrow i j).mp hb
    omega

end Bits

end IntegerMultiplication
end Computability
end OAI
