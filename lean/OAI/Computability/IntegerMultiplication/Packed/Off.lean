import OAI.Computability.IntegerMultiplication.Packed.Sequence

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Dims Adic
variable {H L i : ℕ}
abbrev Triple (T : Type) := T × T × T
abbrev Plate (H L i : ℕ) := Triple (Queue H L i)
def phase (x : Queue H L i) (j : Fin i) :=
  ((x.2.1 j).2.2.val:ℤ)
noncomputable section

-- vector of mask displacements (MSB order segments)
def start (t : Turn) (x y : Queue H L i) :
    Span ℤ i := fun j => compare_ t (phase x j) (totient (y.2.1 j))

def walk (t : Turn) : Equiv.Perm (Plate H L i) :=
  if t.wing = true then
    { toFun p := (p.1,p.2.1,slide (start t p.1 p.2.1) p.2.2)
      invFun p := (p.1,p.2.1,(slide (start t p.1 p.2.1)).symm p.2.2)
      left_inv p := by simp
      right_inv p := by simp }
  else
    { toFun p := (p.1,slide (start t p.1 p.2.2) p.2.1,p.2.2)
      invFun p := (p.1,(slide (start t p.1 p.2.2)).symm p.2.1,p.2.2)
      left_inv p := by simp
      right_inv p := by simp }
-- arbitrary list perm (chronological)
def cruise : List Turn → Equiv.Perm (Plate H L i)
| [] => Equiv.refl _
| h::t => (walk h).trans (cruise t)
theorem last (v : List Turn) (t) (x : Plate H L i) :
    cruise (v++[t]) x = walk t (cruise v x) := by
  induction v generalizing x with
  | nil => rfl
  | cons s v ih =>
    change cruise (v++[t]) (walk s x)=_
    rw [ih]; rfl

abbrev meter (x : Plate H L i) (j : Fin i) : Twirl :=
  (totient (x.2.1.2.1 j),totient (x.2.2.2.1 j))
abbrev tried (x : Plate H L i) (j : Fin i) (t) :=
  dance t (phase x.1 j) (meter x j)
abbrev quiet (x : Queue H L i) := (x.1,x.2.2)

private theorem step (x : Plate H L i) (t : Turn)
    (q : ∀ j, small H L (tried x j t).1 ∧ small H L (tried x j t).2) :
    (walk t x).1=x.1 ∧ (∀ j,meter (walk t x) j=tried x j t) ∧
      quiet (walk t x).2.1=quiet x.2.1 ∧ quiet (walk t x).2.2=quiet x.2.2 := by
  cases e:t.wing
  · choose y h using fun j => represent _ (q j).1
    have move : ∀ j, totient (y j)=totient (x.2.1.2.1 j)+ start t x.1 x.2.2 j :=
      fun j => by simpa only [tried,dance,e,start,Bool.cond_false] using h j
    simp only [walk,e,Bool.false_eq_true,ite_false,Equiv.coe_fn_mk,dress _ y _ move,tried,
      meter,dance,move, start,quiet,Bool.cond_false,true_and,and_true]
    exact fun _ => trivial
  choose y h using fun j => represent _ (q j).2
  have move : ∀ j, totient (y j)=totient (x.2.2.2.1 j)+start t x.1 x.2.1 j :=
    fun j => by simpa only [tried,dance,e,start,Bool.cond_true] using h j
  simp only [walk,e,ite_true,Equiv.coe_fn_mk,dress _ y _ move,tried,
    meter,dance,move,start, quiet,Bool.cond_true,true_and,and_true]
  exact fun _ => trivial
def good (x : Plate H L i) : Prop :=
  ∀ j : Fin i, (8≤(meter x j).1 ∧ (meter x j).1 < (2^width H L:ℕ)-8 -- nat sub? coercions
  ) ∧ (8≤(meter x j).2 ∧ (meter x j).2 < (2^width H L:ℕ)-8)
theorem main (x : Plate H L i) (q : good x) (l : List Turn) (h : l <+: order) :
    (cruise l x).1=x.1 ∧ (∀ j,meter (cruise l x) j = ball (phase x.1 j) (meter x j) l) ∧
    quiet (cruise l x).2.1=quiet x.2.1 ∧ quiet (cruise l x).2.2=quiet x.2.2 := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨rfl,fun _=>rfl,rfl,rfl⟩
  | append_singleton l t ih =>
    obtain ⟨a,b,c,d⟩ := ih (by
      obtain ⟨z,e⟩ := h
      exact ⟨[t]++z,List.append_assoc .. |>.symm.trans e⟩)
    let p := cruise l x
    have f (j) : tried p j t = ball (phase x.1 j) (meter x j) (l++[t]) := by
      rw [tried, ball,List.foldl_append,List.foldl_cons,List.foldl_nil]; rw [show p.1=x.1 from a,b j]
    have u j := stretch (l++[t]) (fun s e => List.IsPrefix.subset h e) (phase x.1 j)
      (meter x j).1 (meter x j).2
    obtain ⟨w,e,m,y⟩ := step p t (fun j => by
      rw [f]
      specialize u j; specialize q j
      have hc : (l++[t]).length≤8 := h.length_le
      simp only [meter] at u q ⊢
      unfold small; omega)
    rw [last]
    exact ⟨w.trans a, fun j => (e j).trans (f j),m.trans c,y.trans d⟩
-- true XOR at bit
def other (a c : Fin 2) : Fin 2 := if c=0 then a else if a=0 then 1 else 0
@[simp] theorem self (a c : Fin 2) :
    other (other a c) c=a := by fin_cases a <;> fin_cases c <;> decide
theorem transition (a c : Fin 2) : ((other a c).val:ℤ) =
    if (c.val:ℤ)=1 then (a.val:ℤ)+ (1-2*((a.val:ℤ)%2)) else (a.val:ℤ) := by
  fin_cases a <;> fin_cases c <;> decide
def guide (x y : Queue H L i) : Queue H L i :=
  (y.1,(fun j => ((y.2.1 j).1,(y.2.1 j).2.1,other (y.2.1 j).2.2 (x.2.1 j).2.2)),y.2.2)
@[simp] theorem guided (x y : Queue H L i) :
    guide x (guide x y)=y := by simp [guide]
def ideal : Equiv.Perm (Plate H L i) where
  toFun p := (p.1,guide p.1 p.2.1,p.2.2)
  invFun p := (p.1,guide p.1 p.2.1,p.2.2)
  left_inv p := by simp
  right_inv p := by simp

private theorem qusame {x y : Queue H L i} (h : quiet x=quiet y)
    (e : ∀ j,totient (x.2.1 j) = totient (y.2.1 j)) : x=y :=
  Prod.ext ((Prod.ext_iff.mp h).1) (Prod.ext (funext (fun j=> unique (e j))) ((Prod.ext_iff.mp h).2))

theorem parallel (x : Plate H L i) (e : good x) : cruise order x=ideal x := by
  obtain ⟨q,v,w,g⟩ := main x e order (by simp)
  refine Prod.ext q (Prod.ext (qusame w fun j=> ?_) (qusame g fun j=>?_))
  · have h := Prod.ext_iff.mp (show meter (cruise order x) j = (if phase x.1 j=1 then
        (meter x j).1+(1-2*((meter x j).1%2)) else (meter x j).1,(meter x j).2) by rw [v,← all])
    refine h.1.trans ?_
    change _= totient ((guide x.1 x.2.1).2.1 j)
    rw [parity]
    change _ = 2* (↑(number (guard H L (x.2.1.2.1 j))):ℤ)+↑(other (x.2.1.2.1 j).2.2 (x.1.2.1 j).2.2).val
    rw [transition]
    unfold phase meter
    rw [parity]
    have hz := Int.add_emod (2*(↑(number (guard H L (x.2.1.2.1 j))):ℤ))
        (↑((x.2.1.2.1 j).2.2.val)) 2
    omega
  · have a := (v j).trans (all ..)
    exact Prod.ext_iff.mp a |>.2
end
end Packed

end IntegerMultiplication
end Computability
end OAI
