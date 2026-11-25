import OAI.Computability.IntegerMultiplication.Cone.Pipe

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Halo
open Param Scale Echo Cap IntegerMultiplication.Fourier Finset
variable (n:ℕ)
abbrev Focn := scouts n
abbrev Scouts := Fin (Focn n)

abbrev sucV := Spot (room n)
abbrev dayV := Spot (wall n)
abbrev primeV := Scouts n→ dayV n
abbrev Jade := primeV n×sucV n×dayV n
abbrev Tri := Vector_ (criterion n)
variable {n} (h:Season n)

def rook (j : Scouts n) : Direction n :=
  ⟨j.val,Nat.lt_of_lt_of_le j.isLt (Nat.sub_le _ _)⟩
def near : Direction n :=
  ⟨Focn n,by have v:= h.dim; unfold Focn scouts; omega⟩
def rear : Direction n :=
  ⟨Focn n+1,by have v:= h.dim; unfold Focn scouts; omega⟩

theorem rook_f (j : Scouts n) : criterion n (rook j)=wall n := by
  apply Eq.trans (sides _ _) (ite_eq_right ?_)
  have v:= j.isLt
  unfold short abbreviated rook
  change j.val ≠ _
  exact Nat.ne_of_lt v
theorem near_s : criterion n (near h)=room n := Eq.trans (sides _ _) (ite_eq_left rfl)
theorem rear_f : criterion n (rear h)=wall n := by
  apply Eq.trans (sides _ _) (ite_eq_right ?_)
  change Focn n+1 ≠ Focn n
  omega

-- induction on directions
include h
theorem cases_ (f:Direction n→Prop) (P:∀j:Scouts n,f (rook j))
    (S:f (near h)) (R:f (rear h)) (i:Direction n) : f i := by
  by_cases k:i.val<Focn n
  · exact P ⟨i.val,k⟩
  by_cases b:i.val=Focn n
  · rwa [show i=near h from Fin.ext b]
  have v:= i.isLt
  have w:= h.dim
  have Q:Focn n=lanes n-2:=rfl
  have A:i=rear h := Fin.ext (show i.val=Focn n+1 by omega)
  rwa [A]

-- positional packing
abbrev splitter (x:Tri n) : Jade n :=
  (fun i=>Fin.cast (rook_f i) (x (rook i)),
    Fin.cast (near_s h) (x (near h)),
    Fin.cast (rear_f h) (x (rear h)))

def numeral (x:Jade n) (i:Direction n):ℕ :=
  if k:i.val<Focn n then (x.1 ⟨i,k⟩).val else if i=near h then x.2.1.val else x.2.2.val

@[simp] theorem numeralP (x:Jade n) (i:Scouts n): numeral h x (rook i)=(x.1 i).val :=
  dite_eq_left i.isLt
@[simp] theorem numeralS (x:Jade n): numeral h x (near h)=x.2.1.val := by
  unfold numeral; rw [dite_eq_right (by exact lt_irrefl _),ite_eq_left rfl]
@[simp] theorem numeralR (x:Jade n): numeral h x (rear h)=x.2.2.val := by
  unfold numeral
  rw [dite_eq_right (by change ¬ Focn n+1<Focn n; omega),ite_eq_right (by
    intro e; have := congrArg Fin.val e
    change Focn n+1=Focn n at this
    omega)]

theorem scope_n (x:Jade n) (i:Direction n): numeral h x i<criterion n i := by
  refine cases_ h (fun i=>numeral h x i<criterion n i) ?_ ?_ ?_ i
  · intro v; rw [numeralP,rook_f]; exact (x.1 v).isLt
  · rw [numeralS,near_s h]; exact x.2.1.isLt
  rw [numeralR,rear_f h]; exact x.2.2.isLt
abbrev gluer (x:Jade n) : Tri n := fun i=> ⟨_,scope_n h x i⟩

def prism : Tri n≃ Jade n where
  toFun := splitter h
  invFun := gluer h
  left_inv x := funext (cases_ h (fun i=> gluer h (splitter h x) i=x i)
    (fun j=>Fin.ext (numeralP h _ j))
    (Fin.ext (numeralS h _))
    (Fin.ext (numeralR h _)))
  right_inv x := Prod.ext (funext fun j=>Fin.ext (numeralP h _ j))
    (Prod.ext (Fin.ext (numeralS h x)) (Fin.ext (numeralR h x)))

-- tensor prod split via image direction type
abbrev rays := Scouts n⊕ Bool -- false short
abbrev senior (i:rays (n:=n)): Direction n :=
  Sum.elim rook (fun b=> bif b then rear h else near h) i
def origin (i:Direction n): rays (n:=n) :=
  if e:i.val<Focn n then Sum.inl ⟨_,e⟩ else Sum.inr (decide (i=rear h))

@[simp] theorem originP (j:Scouts n) : origin h (rook j)=Sum.inl j:= dite_eq_left j.isLt
@[simp] theorem originR : origin h (rear h)=Sum.inr true:= by
  unfold origin; rw [dite_eq_right (by change ¬ Focn n+1<Focn n; omega)]
  simp
@[simp] theorem originS : origin h (near h)=Sum.inr false:= by
  unfold origin; rw [dite_eq_right (by exact lt_irrefl _)]
  simp only [Sum.inr.injEq,decide_eq_false_iff_not]
  intro i; have := congrArg Fin.val i
  change Focn n=Focn n+1 at this; omega

def gallery : rays (n:=n)≃Direction n where
  toFun:=senior h
  invFun:=origin h
  left_inv i := by cases i with
    | inl v=>exact originP h v
    | inr b=> cases b <;> first | exact originR h|exact originS h
  right_inv x := by
    refine cases_ h (fun i=>senior h (origin h i)=i) ?_ ?_ ?_ x
    · intro i; rw [originP]; rfl
    · rw [originS]; rfl
    · rw [originR]; rfl

theorem productF (f:Direction n→ℂ):
    ∏ i,f i=(∏ i:Scouts n,f (rook i))*f (near h)*f (rear h) := by
  rw [← (gallery h).prod_comp f,Fintype.prod_sum_type]
  simp [gallery,senior]
  ring

theorem sums_ (f:Tri n→ℂ):
    ∑ i,f i=
      ∑ a:primeV n,∑ b:sucV n,∑ c:dayV n,f (gluer h (a,b,c)) := by
  rw [← (prism h).symm.sum_comp f,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rfl
end Halo

end IntegerMultiplication
end Computability
end OAI
