import OAI.Computability.NearSquareRoot.CRTTableStageMachine
import OAI.Computability.NearSquareRoot.BoxFin

/-! # Correct ordered CRT switch programs for the generated mixed-radix box -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

/-- Binary coordinate width of an axis of the generated box. -/
def axisWidth (box : List (ℕ × ℕ)) (g : Fin box.length) := (box.get g).1

private theorem fitsBox {k l : ℕ} {box : List (ℕ × ℕ)} (h : BoxShape.Valid k l box)
    (g : Fin box.length) : BoxFin.modulus box g ≤ 2 ^ axisWidth box g :=
  (h.axisBounds _ (List.get_mem box g)).2.2.2

/-- The switches really realize the full padded CRT or its inverse for every
such box. Density supplies the upper bound on the padding required by the
bounded unary program. -/
theorem boxSwitches_run {k l : ℕ} {box : List (ℕ × ℕ)} (h : BoxShape.Valid k l box) (inv : Bool) :
    let a := BoxFin.modulus box
    let w := axisWidth box
    letI : ∀ g, NeZero (a g) := BoxFin.modulus_neZero h
    ∀ x : (g : Fin box.length) → AxisValue a w g,
    (switchOrder box.length l inv).foldl (fun y s => switchPerm a w (fitsBox h) inv s y) x =
      (bif inv then (CRT.paddedPermutation a (fun g => Fin (BoxFin.padding box g))).symm
       else CRT.paddedPermutation a (fun g => Fin (BoxFin.padding box g))) x := by
  dsimp only
  let := BoxFin.modulus_neZero h
  exact switchOrder_run (BoxFin.modulus box) (axisWidth box) (fitsBox h)
    (fun g => axis_half_full h (List.get_mem box g)) (BoxFin.pairwise h) l
    (fun g => (h.axisBounds _ (List.get_mem box g)).2.1) inv

/-- Shape, validity, and every switch equality simultaneously, for every
sufficiently large original address width and with the box computed from
that width by the parameter program. -/
theorem eventually_boxSwitches :
    ∃ K : ℕ, ∀ k ≥ K, ∃ h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k),
      let box := CoprimeBox.box k
      let a := BoxFin.modulus box
      let w := axisWidth box
      letI : ∀ g, NeZero (a g) := BoxFin.modulus_neZero h
      ∀ (inv : Bool) (x : (g : Fin box.length) → AxisValue a w g),
      (switchOrder box.length (BoxScale.width k) inv).foldl
          (fun y s => switchPerm a w (fitsBox h) inv s y) x =
        (bif inv then (CRT.paddedPermutation a (fun g => Fin (BoxFin.padding box g))).symm
         else CRT.paddedPermutation a (fun g => Fin (BoxFin.padding box g))) x := by
  obtain ⟨K,H⟩ := CoprimeBox.eventually_valid
  exact ⟨K, fun k hk => ⟨H k hk, boxSwitches_run (H k hk)⟩⟩

end CRTTable

end NearSquareRoot
end Computability
end OAI
