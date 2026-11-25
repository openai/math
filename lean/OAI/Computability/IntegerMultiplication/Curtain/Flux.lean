import OAI.Computability.IntegerMultiplication.Curtain.Lace

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Curtain.Pin
open Net.Walsh Net.Tensor Finset Matrix
variable {J F U R:Type} [Fintype J] [DecidableEq J] [Fintype F] [Fintype U]
variable [CommRing R] (c : Quarter R)
variable (p : Pin J F U)
omit [DecidableEq J] in
theorem Walsh_at (x y : Addr J) :
    (WalshM : Net.Walsh.Field J R) x y = c.ph (exp2 (x ⬝ᵥ y)) := by
  simp only [WalshM,Net.Tensor.app,dotProduct,map_sum,c.of_sum]
  apply Finset.prod_congr rfl
  intro i _
  rcases bit_value (x i * y i) with h|h
  · show (if x i*y i=1 then -1 else 1) = _
    rw [h,show exp2 0=0 by decide,c.null,ite_eq_right (by decide)]
  show (if x i*y i=1 then -1 else 1) = _
  rw [h,show exp2 1=2 by decide, c.moon, ite_eq_left rfl]

def charm : Net.Walsh.Field J R := WalshM * diagonal (D c p)
def bar : Net.Walsh.Field J R := WalshI c * diagonal (D c p)

@[simp] theorem chi (x y : Addr J) :
    charm c p x y = WalshM x y * D c p y := by
  simp [charm,Matrix.mul_apply,Matrix.diagonal_apply]
@[simp] theorem rho (x y : Addr J) :
    bar c p x y = WalshI c x y * D c p y := by
  simp [bar,Matrix.mul_apply,Matrix.diagonal_apply]
-- complete square reindex
private def shad (x : Addr J) : Equiv.Perm (Addr J) :=
  {
    toFun := fun y => y+x
    invFun := fun y => y+x
    left_inv y := by simp [add_assoc]
    right_inv y := by simp [add_assoc]
  }
-- square entries via translation sum
theorem f2 (x y : Addr J) :
    (charm c p * charm c p) x y =
      G c p * c.ph (-q p x) * WalshM (ret p x) y := by
  let t := ret p (x+y)
  have z (b : Addr J) :
      charm c p x b * charm c p b y =
        D c p (b+t)*c.ph (-q p x)*WalshM (ret p x) y := by
    simp_rw [chi,Walsh_at c, D,← c.of_add]
    apply congrArg c.ph
    rw [quadr p, show ret p t = x+y from retain p _, q_s p,quadr p,
        dotProduct_add,map_add,dotProduct_comm x, p_ret]
    have : -(exp2 (ret p x ⬝ᵥ y):Clock) = exp2 (ret p x ⬝ᵥ y) := by
      generalize ret p x ⬝ᵥ y = w
      revert w; decide
    -- Clock Abel. Q(b+t)=q b + q x + q y + exp2 xPy + exp2 b(x+y), double
    nth_rw 1 [← this]
    abel
  rw [Matrix.mul_apply]
  simp_rw [z]
  rw [← Finset.sum_mul,← Finset.sum_mul]
  exact congrArg (fun b=> b * _ * _) (Equiv.sum_comp (shad t) (D c p))

theorem f3 (x y : Addr J) :
    (charm c p * charm c p * bar c p) x y =
      if ret p x=y then G c p else 0 := by
  have h := congrFun (congrFun (WM c (J:=J)) (ret p x)) y
  rw [Matrix.mul_apply,Matrix.one_apply] at h
  rw [Matrix.mul_apply]
  simp_rw [rho,f2]
  have e (b : Addr J) : G c p*c.ph (-q p x)*WalshM (ret p x) b *
        (WalshI c b y*D c p y) =
      (G c p * c.ph (-q p x)*D c p y) * (WalshM (ret p x) b * WalshI c b y) := by ring
  simp_rw [e,← Finset.mul_sum,h]
  split
  next yy =>
    rw [← yy,mul_one,D,q_s,mul_assoc,← c.of_add,neg_add_cancel,c.null,mul_one]
  simp

def gloss : R := c.streak false^Fintype.card F * c.half^Fintype.card U

theorem slake : c.streak false * (1+c.i) = 1 := by
  unfold Quarter.streak
  simp only [Bool.false_eq_true, ite_false]
  rw [mul_assoc, show ((1-c.i)*(1+c.i))=(2:R) from by linear_combination -c.ii, mul_comm, c.twice'']

theorem dull [DecidableEq F] [DecidableEq U] :
    gloss (F:=F) (U:=U) c * G c p = 1 := by
  rw [gloss,gauss_lace]
  rw [show c.streak false^Fintype.card F *
    c.half^Fintype.card U *
    ((1+c.i)^Fintype.card F * (2:R)^Fintype.card U)=
    (c.streak false^Fintype.card F * (1+c.i)^Fintype.card F) *
    ((2:R)^Fintype.card U * c.half^Fintype.card U) from by ring,← mul_pow,← mul_pow,c.twice'',slake]
  simp
end Curtain.Pin

end IntegerMultiplication
end Computability
end OAI
