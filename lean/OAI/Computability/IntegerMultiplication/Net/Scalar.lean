import OAI.Computability.IntegerMultiplication.Net.Weight

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Walsh
open Finset
structure Quarter (R : Type) [CommRing R] where
  i : R
  half : R
  ii : i*i = -1
  two : half+half = 1
namespace Quarter
variable {R : Type} [CommRing R] (c : Quarter R)
theorem twice (x : R) : c.half*x + c.half*x = x := by rw [← add_mul,c.two,one_mul]
theorem twice' (x : R) : c.half*x*2=x := by rw [mul_two,c.twice]
theorem twice'' : 2*c.half=1 := by rw [two_mul,c.two]

def ph (j : Clock) : R := if j=0 then 1 else if j=1 then c.i else if j=2 then -1 else -c.i

theorem four (j : Clock) : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by revert j; decide
theorem of_add (a b : Clock) : c.ph (a+b) = c.ph a * c.ph b := by
  rcases four a with ea|ea|ea|ea
  all_goals rcases four b with eb|eb|eb|eb
  all_goals
    rw [ea,eb]
    simp (config := {decide:=true}) [ph,c.ii]
@[simp] theorem null : c.ph 0 = 1 := rfl
@[simp] theorem bright : c.ph 1 = c.i := rfl
theorem moon : c.ph 2 = -1 := rfl
theorem back : c.ph (-1) = -c.i := rfl

theorem of_sum {J} (s : Finset J) (k : J → Clock) :
    c.ph (∑ j∈s, k j) = ∏ j∈s, c.ph (k j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx,Finset.prod_insert hx,c.of_add,ih]

def raySign (x : B) : R := if x=0 then 1 else -1
@[simp] theorem sing : raySign (R:=R) 1 = -1 := by simp [raySign, show (1:B)≠0 by decide]
@[simp] theorem fine : raySign (R:=R) 0 = 1 := ite_eq_left rfl
theorem shift (x : B) : c.ph (exp2 x) = raySign x := by
  rcases bit_value x with e|e <;> subst x <;> rfl

theorem reverseSign (x : B) : c.ph (-exp2 x) = raySign x := by
  have hh : ∀ x, (-exp2 x : Clock)=exp2 x := by decide
  rw [hh, shift]

def glaze (invert : Bool) :=
  c.half * (1 + (if invert then -c.i else c.i))
def streak (invert : Bool) :=
  c.half * (1 - (if invert then -c.i else c.i))

theorem offOn (v : B) (k : Clock) (h : k=1 ∨ k=(-1:Clock)) :
    c.ph (k*digit v) = c.glaze (decide (k ≠ 1)) +
      c.streak (decide (k≠1)) * raySign v := by
  have n : (-1:Clock) ≠ 1 := by decide
  rcases h with h|h <;> rcases bit_value v with hv|hv <;> subst k <;> subst v
  all_goals
    simp [glaze,streak, digit,n,back]
  all_goals
    simp only [mul_add,mul_sub,mul_one]
    have h1 := c.two
    have h2 := c.twice c.i
    have h3 := c.twice (-c.i)
    simp only [mul_neg] at *
    abel_nf at *
    first | exact h1.symm | exact h2.symm | exact h3.symm
end Quarter
end Net.Walsh

end IntegerMultiplication
end Computability
end OAI
