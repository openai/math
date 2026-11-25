import OAI.Computability.IntegerMultiplication.Net.Butter

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Walsh
open Finset Matrix Tensor Quarter
variable {J R : Type} [Fintype J] [DecidableEq J] [CommRing R] (c : Quarter R)
abbrev Field (J R : Type) := Mat (Addr J) R
def WalshM : Field J R := mat (fun _ => F)
def WalshI : Field J R := mat (fun _ => Fb c)
def through (d : Addr J → R) : Field J R := WalshM * Matrix.diagonal d * WalshI c
def oscillate (g : Addr J → Clock) : Field J R := through c (c.ph ∘ g)
theorem Wi : (WalshI (J:=J) c) * WalshM = 1 := by
  rw [WalshI, WalshM, multiply]; simpa [settle] using Tensor.unit (I:=J) (J:=B) (R:=R)
theorem WM : WalshM * WalshI (J:=J) c = 1 := by
  rw [WalshI,WalshM,multiply]; simpa [collapse] using Tensor.unit (I:=J) (J:=B) (R:=R)

@[simp] theorem common (x : R) : through c (fun _ : Addr J => x) = x • 1 := by
  have d : Matrix.diagonal (fun _ : Addr J => x) = x • 1 := by
    ext i j; by_cases e : i=j <;> simp [e]
  rw [through,d, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, WM c]

theorem through_sep (d : J → B → R) : through c (vec d) =
    mat (fun j => F * Matrix.diagonal (d j) * Fb c) := by
  rw [through,← Tensor.diag,WalshM,WalshI,multiply,multiply]
theorem through_add (d e : Addr J → R) : through c (d+e) = through c d + through c e := by
  unfold through
  rw [show diagonal (d+e) = diagonal d + diagonal e from (Matrix.diagonal_add d e).symm]
  simp only [Matrix.mul_add, Matrix.add_mul]
theorem through_scale (r : R) (d : Addr J → R) : through c (r • d) = r • through c d := by
  simp [through]
theorem through_mul (d e : Addr J → R) :
    through c d * through c e = through c (d*e) := by
  unfold through
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc (WalshM * diagonal d) (WalshI c), Wi c, Matrix.mul_one,
    Matrix.mul_assoc WalshM (Matrix.diagonal d) (Matrix.diagonal e), Matrix.diagonal_mul_diagonal]
  rfl

@[simp] theorem osc_zero : oscillate c (0 : Addr J → Clock) = 1 := by
  have t : c.ph ∘ (0 : Addr J → Clock) = fun _ => (1:R) := by ext; simp
  rw [oscillate,t,common,one_smul]
theorem osc_add (d e : Addr J → Clock) :
    oscillate c d * oscillate c e = oscillate c (d+e) := by
  unfold oscillate; rw [through_mul]
  congr 1; funext; simp [c.of_add]
theorem between (d e : Addr J → Clock) :
    oscillate c d * oscillate c (-e) = oscillate c (d-e) := by rw [osc_add, sub_eq_add_neg]

def shade (v : Addr J) : Field J R := Matrix.of fun x y => if y=x+v then 1 else 0
-- directly the tensor of swaps on v
omit [DecidableEq J] in
theorem shade_split (v : Addr J) : shade (R:=R) v = mat (fun j => SwapBy (v j)) := by
  ext x y
  unfold shade SwapBy
  simp_rw [app, of_apply, Tensor.prod_indicator (R:=R)]
  simp [funext_iff]

def modulate (v : Addr J) : Addr J → R :=
  fun x => raySign (v ⬝ᵥ x)
theorem through_cover (v : Addr J) : through c (modulate v) = shade v := by
  have d : modulate (R:=R) v = Tensor.vec (fun j x => raySign (v j*x)) := by
    funext x
    simp only [modulate, ← c.shift, dotProduct, map_sum, c.of_sum, Tensor.vec]
  rw [d, through_sep, shade_split]
  congr 1
  funext j
  rcases bit_value (v j) with h|h <;> rw [h,runBy]
  · simp [collapse]
  simp
  exact found c

def kernel (inverted : Bool) (v : Addr J) : Field J R :=
  c.glaze inverted • 1 + c.streak inverted • shade v
@[simp] theorem kernel_at (inv : Bool) (v : Addr J) (f : Vec (Addr J) R) (x) :
    (kernel c inv v *ᵥ f) x = c.glaze inv * f x + c.streak inv * f (x+v) := by
  rw [kernel, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
  simp [shade,mulVec,dotProduct,Pi.smul_apply,smul_eq_mul]

theorem kernel_osc (a : Clock) (h : a=1 ∨ a=(-1:Clock)) (v : Addr J) :
    oscillate c (fun x => a*digit (v ⬝ᵥ x)) = kernel c (decide (a≠1)) v := by
  let b := decide (a≠1)
  unfold oscillate
  rw [show c.ph ∘ (fun x => a*digit (v ⬝ᵥ x)) =
    (fun (_ : Addr J) => c.glaze b) + c.streak b • modulate v by
      funext; exact c.offOn _ _ h,
      through_add,through_scale,common,through_cover]
  rfl
end Net.Walsh

end IntegerMultiplication
end Computability
end OAI
