import OAI.Computability.IntegerMultiplication.Net.Scalar

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Walsh
open Finset Matrix Tensor Quarter
variable {R : Type} [CommRing R] (c : Quarter R)

theorem duo (g : B → R) : ∑ i, g i = g 0 + g 1 := by
  -- univ B equality via decide
  change Finset.sum (univ : Finset B) g = _
  rw [show (univ : Finset B)={0,1} by decide, Finset.sum_insert (by decide),Finset.sum_singleton]

def Z : Mat B R := Matrix.diagonal Quarter.raySign
def X : Mat B R := Matrix.of fun x y => if x = y then 0 else 1
def F : Mat B R := Matrix.of fun x y => if x*y=1 then -1 else 1
def A (inv : Bool) : Mat B R := Matrix.of fun x y => if x=y then c.glaze inv else c.streak inv
def Fb := c.half • (F : Mat B R)
def SwapBy (v : B) : Mat B R := Matrix.of fun x y => if y=x+v then 1 else 0
def Violet (inv : Bool) := Matrix.diagonal fun x : B =>
  c.ph ((if inv then (-1:Clock) else 1)*digit x)

theorem collapse : F * Fb c = 1 := by
  ext i j; rcases bit_value i with e|e <;> rcases bit_value j with h|h <;> subst i <;> subst j
  all_goals
    simp (config := {decide:=true}) [F,Fb,Matrix.mul_apply, duo, c.two]
  exact c.twice''

theorem settle : Fb c * F = 1 := mul_eq_one_comm.mp (collapse c)

theorem found : F * (Z : Mat B R) * Fb c = X := by
  ext i j; rcases bit_value i with e|e <;> rcases bit_value j with h|h <;> subst i <;> subst j
  all_goals
    simp (config := {decide:=true}) [F,Fb,Z,X,Matrix.diagonal_apply, Matrix.mul_apply, duo, raySign,c.two]

theorem burn (inv : Bool) : F * Violet c inv * Fb c = A c inv := by
  have no : (-1:Clock) ≠ 1 := by decide
  ext i j; rcases bit_value i with e|e <;> rcases bit_value j with h|h <;> subst i <;> subst j
  all_goals cases inv
  all_goals
    simp (config := {decide:=true}) [F,Fb,Violet,A,glaze,streak,Matrix.diagonal_apply,
      Matrix.mul_apply, duo, digit, c.back]; ring

theorem runBy (v : B) : (SwapBy v : Mat B R) = if v=0 then 1 else X := by
  ext i j
  rcases bit_value v with a|a <;> rcases bit_value i with e|e <;> rcases bit_value j with h|h
  all_goals subst_vars; simp (config := {decide:=true}) [SwapBy,X]

theorem tangle (inv : Bool) :
    A c inv = c.glaze inv • 1 + c.streak inv • X := by
  ext i j
  by_cases e : i=j <;> simp [A,X,e]

-- forward/inverse wrappers and ordinary Walsh gate
theorem adjust (inv : Bool) :
    (if inv then -c.i else c.i) • (Z * A c (!inv) * Z) = A c inv := by
  ext i j
  have sq : c.i^2 = -1 := by rw [pow_two,c.ii]
  rcases bit_value i with a|a <;> rcases bit_value j with b|b
  all_goals cases inv; all_goals
    subst_vars
    simp (config := {decide:=true}) [Z,A,glaze,streak,Matrix.diagonal_apply,Matrix.mul_apply,duo,
      raySign]
  all_goals first | linear_combination c.half*sq | linear_combination -c.half*sq

theorem ordinary : c.streak false • (Violet c false * A c false * Violet c false) = Fb c := by
  have sq : c.i^2 = -1 := by rw [pow_two,c.ii]
  ext i j
  rcases bit_value i with a|a <;> rcases bit_value j with b|b
  all_goals
    subst_vars
    simp (config := {decide:=true}) [Violet,A,Fb,F,glaze,streak,Matrix.diagonal_apply,Matrix.mul_apply,
      duo,digit]
  -- derive algebra
  all_goals
    have h1 : (1-c.i)*(1+c.i) = 2 := by linear_combination -sq
    have h2 : (1-c.i)*(1-c.i)*c.i = 2 := by linear_combination (c.i-2)*sq
  · calc
      _ = c.half*(c.half*((1-c.i)*(1+c.i))) := by ring
      _ = _ := by rw [h1,mul_comm _ 2,c.twice'',mul_one]
  · calc
      _ = c.half*(c.half*((1-c.i)*(1-c.i)*c.i)) := by ring
      _ = _ := by rw [h2,mul_comm _ 2,c.twice'',mul_one]
  · calc
      _ = c.half*(c.half*((1-c.i)*(1-c.i)*c.i)) := by ring
      _ = _ := by rw [h2,mul_comm _ 2,c.twice'',mul_one]
  calc
    _ = c.half*(c.half*((1-c.i)*(1+c.i)))*(c.i*c.i) := by ring
    _ = _ := by rw [h1,mul_comm _ 2,c.twice'',mul_one,c.ii]; simp
end Net.Walsh

end IntegerMultiplication
end Computability
end OAI
