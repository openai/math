import OAI.Computability.IntegerMultiplication.Carry.Accum

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Carry
open Code Bits
-- if divide by zero, branch explicitly
abbrev Wstep := Word × Two × Bool
abbrev twice_ (p:Wstep) := p.2.2::p.2.1.2
abbrev borrow_ (p:Wstep) := Bits.sub (twice_ p,p.1)
def quest (p: Wstep) : Two :=
  let z := borrow_ p
  bif z.2 then (false::p.2.1.1,twice_ p) else (true::p.2.1.1,z.1)
@[fun_prop] theorem polyQuest : Poly quest := by
  unfold quest borrow_ twice_
  fun_prop

private theorem sizeQuest (u:Word) (t:Two) (b:Bool) :
    size (quest (u,t,b)) ≤ size t+8*(size u+size b) := by
  unfold quest borrow_ twice_
  dsimp only
  cases h:(Bits.sub (b::t.2,u)).2
  all_goals simp only [Bool.cond_true,Bool.cond_false,size_prod,sub_length,size_word,List.length_cons,
    show size b=1 from rfl]; omega
def divide (p:Two) : Two := trek quest (p.1.reverse,p.2,([]:Word),([]:Word))
@[fun_prop] theorem polyDivide : Poly divide := by
  unfold divide
  exact Poly.compose (show Poly (fun p:Two=> (p.1.reverse,p.2,([]:Word),([]:Word))) from by fun_prop) (polyTrek _ polyQuest 8 sizeQuest)
theorem divide_nil (p:Word): divide ([],p)=([],[]) := rfl
theorem divide_cons b (x y:Word):
    divide (b::x,y)=quest (y,divide (x,y),b) := by simp [trek,divide,List.foldl_append]

theorem divides (x y:Word) (h:0<value y):
    let s := divide (x,y)
    value s.1 * value y+ value s.2=value x ∧ value s.2 < value y := by
  induction x with
  | nil=> simp [divide_nil,h]
  | cons b x ih =>
    rw [divide_cons]
    let s:= divide (x,y)
    let t:=b::s.2
    let g:=Bits.sub (t,y)
    change _*value y+_= _ ∧ _ < value y
    unfold quest borrow_
    dsimp only
    have e : value t=digit b+2*value s.2 := rfl
    change value s.1*value y+value s.2=value x ∧ value s.2 < value y at ih
    cases h':g.2 with
    | true=>
      change value ((bif true then (false::s.1,t) else (true::s.1,g.1)).1)*_+
        value ((bif true then (false::s.1,t) else (true::s.1,g.1)).2)=_ ∧ value ((bif true then (false::s.1,t) else (true::s.1,g.1)).2)<_
      have h₁:= (sub_borrow t y).mp h'

      simp only [Bool.cond_true,value_cons,d0,e]
      rw [zero_add,Nat.mul_assoc]
      omega
    | false=>
      change value ((bif false then (false::s.1,t) else (true::s.1,g.1)).1)*_+
        value ((bif false then (false::s.1,t) else (true::s.1,g.1)).2)=_ ∧ value ((bif false then (false::s.1,t) else (true::s.1,g.1)).2)<_
      have h₁ : value y ≤ value t := by
        apply le_of_not_gt; intro u; have z : g.2=true := (sub_borrow t y).mpr u
        simp_all
      have q : value g.1+value y = value t := by unfold g; rw [sub_val_le _ _ h₁,Nat.sub_add_cancel h₁]

      simp only [Bool.cond_false,value_cons,d1,Nat.add_mul,Nat.mul_assoc,Nat.one_mul]
      have v := digit_le b
      omega

def nat_div (p:Two):Two :=
  bif lt_ ([],p.2) then divide p else (([]:Word),p.1)
@[fun_prop] theorem polyND : Poly nat_div := by unfold nat_div; fun_prop

theorem division_rules (x y:Word) :
    let s:=nat_div (x,y)
    value s.1=value x / value y ∧ value s.2=value x % value y := by
  by_cases h:0<value y
  · have i : lt_ ([],y)=true := by rw [lt_r, decide_eq_true_eq]; exact h
    rw [nat_div,i]; dsimp only
    simp only [Bool.cond_true]
    obtain ⟨t,a⟩ := divides x y h
    let s:=divide (x,y)
    -- use Nat add-mul lemmas
    rw [← t,Nat.add_comm _ (value _),Nat.mul_comm _ (value y),Nat.add_mul_mod_self_left,Nat.add_mul_div_left _ _ h,Nat.div_eq_of_lt a,Nat.mod_eq_of_lt a,Nat.zero_add]
    exact ⟨rfl,rfl⟩
  have z:value y=0:=by omega
  unfold nat_div; simp [lt_r,z]
end Carry

end IntegerMultiplication
end Computability
end OAI
