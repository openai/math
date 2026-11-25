import OAI.Computability.NearSquareRoot.InterchangeROMTableSpelling

/-! # Matrix table rows in native interchange serialization order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

variable {K L : Type} {p : ℕ}

/-- The input and output axes have independently supplied physical orders. -/
def orderedCoefficients (input : Series K) (output : Series L) (M : Matrix L K (ZMod p)) :
    List (List ℕ) := output.tab fun i => input.tab fun j => (M i j).val

private theorem tab_ofFn {A B : Type} (s : Series A) (f : A → B) :
    List.ofFn (fun i => f (s.follow i)) = s.tab f := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp [Series.tab,Series.follow]
  rfl

private theorem ordered_mulVec [Fintype K] (input : Series K) (output : Series L)
    (M : Matrix L K (ZMod p)) (x : K → ZMod p) (i : Fin output.count) :
    Matrix.mulVec (fun i j => M (output.follow i) (input.follow j)) (x ∘ input.follow) i =
      M.mulVec x (output.follow i) := by
  change (∑ j, M (output.follow i) (input.follow j) * x (input.follow j)) =
    ∑ j, M (output.follow i) j * x j
  exact input.index.symm.sum_comp (fun j => M (output.follow i) j * x j)

/-- A generated numeric matrix table acts on the native P192 stripe for each
enumerated ground ring row, including non-canonical row orders. -/
theorem ordered_correct [NeZero p] [Fintype K] (input : Series K) (output : Series L)
    (M : Matrix L K (ZMod p)) (x : K → ZMod p) :
    let t := matrixTable p input.count (orderedCoefficients input output M)
    let u := stripe input (fun j => numeral (x j).val)
    let v := stripe output (fun i => numeral (M.mulVec x i).val)
    RegisterLookup.read t u = v ∧ (u,v) ∈ t := by
  let M' : Matrix (Fin output.count) (Fin input.count) (ZMod p) :=
    fun i j => M (output.follow i) (input.follow j)
  have H := matrixTable_correct M' (x ∘ input.follow)
  have em : (List.ofFn fun i => residues (M' i)) = orderedCoefficients input output M := by
    calc
      _ = List.ofFn (fun i => input.tab (fun j => (M (output.follow i) j).val)) :=
        congrArg (fun f => List.ofFn f) (funext fun i => tab_ofFn input (fun j => (M (output.follow i) j).val))
      _ = _ := tab_ofFn output (fun i => input.tab fun j => (M i j).val)
  have word {S : Type} (order : Series S) (v : S → ZMod p) :
      numeralWord (residues (v ∘ order.follow)) = stripe order (fun j => numeral (v j).val) := by
    simp only [numeralWord,residues,Function.comp_apply]
    rw [tab_ofFn order (fun j => (v j).val)]
    simp only [Series.tab,Task.forest_map,stripe_simple]
  have ei := word input x
  have hfun : M'.mulVec (x ∘ input.follow) = (M.mulVec x) ∘ output.follow :=
    funext (ordered_mulVec input output M x)
  have eo := word output (M.mulVec x)
  rw [← hfun] at eo
  dsimp only at H
  rw [em,ei,eo] at H
  exact H

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
