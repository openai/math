import OAI.Computability.IntegerMultiplication.Net.Spectrum

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Walsh
open Matrix Tensor Finset Quarter
variable {J R : Type} [Fintype J] [DecidableEq J] [CommRing R] (c : Quarter R)

-- tensor product of direction shifts in every address bit. The weight flips
-- sign on coordinates in partnership with the endpoint correction vector.
def tint (q : Addr J) (x : Addr J) := weight x + exp2 (q ⬝ᵥ x)

omit [DecidableEq J] in
theorem amber (x q : Addr J) : tint q x =
    ∑ j, (if q j = 0 then (1:Clock) else -1)*digit (x j) := by
  unfold tint weight
  rw [dotProduct,map_sum,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  have d : ∀ a b : B, digit a + exp2 (b*a) =
      (if b=0 then (1:Clock) else -1)*digit a := by decide
  intro j _; exact d _ _

omit [DecidableEq J] in
theorem neutral (x : Addr J) : tint 0 x = weight x := by simp [tint]
-- no assumption even on q's norm
theorem prism (q : Addr J) :
    oscillate c (tint q) = mat (fun j : J => A c (decide (q j ≠ 0))) := by
  let d := fun j x => c.ph ((if q j=0 then (1:Clock) else -1)*digit x)
  rw [oscillate, show c.ph ∘ tint q = Tensor.vec d by funext; rw [Function.comp_apply, amber,c.of_sum]; rfl,
    through_sep]
  congr 1; funext j
  by_cases h : q j = 0
  · simpa [d,h,Violet] using burn c false
  simpa [d,h,Violet] using burn c true

-- true unnormalized Hadamard via completed forward. Correction wrappers
-- swap inversion profile inv ↦ flipped inv (arbitrary by using identity
-- per coord where not flipped). ASM can generate diagonal multipliers.
def allC (inv : J → Bool) : Walsh.Field J R := mat fun j => A c (inv j)
theorem extract (q : Addr J) :
    oscillate c (tint q) = allC c (fun j => decide (q j≠0)) := prism c _
theorem evaluate :
    oscillate c (weight (J:=J)) = allC c (fun _ => false) := by
  rw [show (weight (J:=J)) = tint 0 from (funext neutral).symm, extract]
  simp

theorem combine_scale {I A : Type} [Fintype I]
    (c : I → R) (M : I → Mat A R) :
    mat (fun j => c j • M j) = (∏ i, c i) • mat M := by
  ext x y
  simp [mat, Finset.prod_mul_distrib]

def swapSignVec (hit : J → Bool) (x : Addr J) : R :=
  ∏ j, if hit j then raySign (x j) else 1
def pack (hit : J → Bool) := ∏ j, if hit j then c.i else 1

-- correct mixed inverse A outputs to forward A
theorem wrap (hit : J → Bool) :
    (pack c hit) • (Matrix.diagonal (swapSignVec hit) *
      allC c hit * Matrix.diagonal (swapSignVec hit)) = allC c (fun _ => false) := by
  let ss := fun j : J => if hit j then (Z : Mat B R) else 1
  have se : Matrix.diagonal (swapSignVec (R:=R) hit) = mat ss := by
    let g : J → B → R := fun j x => if hit j then raySign x else 1
    rw [show (swapSignVec (R:=R) hit) = Tensor.vec g from rfl, ← Tensor.diag g]
    congr 1; funext j
    cases e : hit j <;> simp [g,e,ss,Z]
  rw [allC,allC,se,multiply,multiply,pack, ← combine_scale]
  congr 1
  funext i
  cases e : hit i
  · simp [ss,e]
  simpa [ss,e] using adjust c false

-- Wrapper for computing inverse from forward
theorem unwrap :
    (∏ _ : J, (-c.i)) •
      (Matrix.diagonal (swapSignVec (fun _ : J => true)) *
      allC c (fun _ => false) * Matrix.diagonal (swapSignVec (fun _ => true))) =
      allC c (fun _ => true) := by
  have se : Matrix.diagonal (swapSignVec (R:=R) (fun _ : J => true)) = mat (fun _ : J => (Z : Mat B R)) := by
    let g : J → B → R := fun _ => raySign
    rw [show swapSignVec (fun _ : J => true) = Tensor.vec g from rfl, ← Tensor.diag g]; rfl
  rw [allC,allC,se,multiply,multiply,← combine_scale]
  congr 1; funext j
  simpa using adjust c true

def bow (x : Addr J) : R := c.ph (weight x)
theorem ordinary_layer :
    (c.streak false ^ Fintype.card J) •
      (Matrix.diagonal (bow c) * allC c (fun _ : J => false) * Matrix.diagonal (bow c)) =
      WalshI c := by
  have be : Matrix.diagonal (bow (J:=J) c) = mat (fun _ : J => Violet c false) := by
    let g : J → B → R := fun _ x => c.ph (digit x)
    rw [show bow c = Tensor.vec g by funext x; unfold bow weight; rw [c.of_sum]; rfl,
      ← Tensor.diag]
    congr 1; funext j
    simp [g,Violet]
  rw [be,allC,multiply,multiply,show c.streak false ^ Fintype.card J = ∏ _ : J, c.streak false by simp,
    ← combine_scale,WalshI]
  congr 1; funext j; exact ordinary c

omit [DecidableEq J] in
theorem unnormalize :
    (2 : R)^Fintype.card J • (WalshI (J:=J) c) = WalshM := by
  rw [show (2 : R)^Fintype.card J = ∏ _ : J, (2:R) by simp, WalshI,← combine_scale,WalshM]
  congr 1
  funext
  rw [Fb,smul_smul,c.twice'',one_smul]
end Net.Walsh

end IntegerMultiplication
end Computability
end OAI
