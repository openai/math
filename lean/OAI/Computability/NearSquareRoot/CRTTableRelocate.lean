import OAI.Computability.NearSquareRoot.CRTTableBenesQuery
import OAI.Computability.NearSquareRoot.CRTControlledBenesMask

/-! # Transporting a CRT header to a prepared prefix and a selected batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

private def remapPositions (x : List Tally × List Tally) : List Tally :=
  polyPush (Iter.pick ([] : Tally)) x

private theorem remapPositions_poly : Poly remapPositions :=
  Poly.push [] [] (Iter.facile ([] : Tally)).poly

private def remapBlock (p : List Tally × Benes.BlockPlan TargetTag) : Benes.BlockPlan TargetTag :=
  (p.2.1,p.2.2.1,remapPositions (p.1,p.2.2.2))

private theorem remapBlock_poly : Poly remapBlock := by
  let X := List Tally × Benes.BlockPlan TargetTag
  have f := (show Poly (fun p : X => (p.1,p.2.2.2)) by fun_prop).compose remapPositions_poly
  exact (show Poly (fun p : X => p.2.1) by fun_prop).pair
    ((show Poly (fun p : X => p.2.2.1) by fun_prop).pair f)

private def emptyBlock : Benes.BlockPlan TargetTag := ((([],[]),false,[],[]),[],[])

/-- The first list supplies new bit locations indexed by natural bit position.
The second supplies natural block numbers in the order of the prepared slots.
All reads and writes operate on the serialized tables. -/
def relocate (p : Benes.BatchPlan TargetTag × List Tally × List Tally) : Benes.BatchPlan TargetTag :=
  let chosen := polyPush (Iter.pick emptyBlock) (p.1.2,p.2.2)
  ((p.1.1.1,p.1.1.2.1,remapPositions (p.2.1,p.1.1.2.2)),polyPush remapBlock (p.2.1,chosen))

theorem relocate_poly : Poly relocate := by
  let X := Benes.BatchPlan TargetTag × List Tally × List Tally
  have picked := (show Poly (fun p : X => (p.1.2,p.2.2)) by fun_prop).compose
    (Poly.push [] [] (Iter.facile emptyBlock).poly)
  have positions := (show Poly (fun p : X => (p.2.1,p.1.1.2.2)) by fun_prop).compose remapPositions_poly
  have blocks := ((show Poly (fun p : X => p.2.1) by fun_prop).pair picked).compose
    (Poly.push [] emptyBlock remapBlock_poly)
  exact ((show Poly (fun p : X => p.1.1.1) by fun_prop).pair
    ((show Poly (fun p : X => p.1.1.2.1) by fun_prop).pair positions)).pair blocks

/-- A directory only needs to cover the bit positions the batch actually
reads, including the external controls. The selected block list may use any
order, so independent groups can be staged separately. -/
theorem relocate_makePlan {N M : ℕ} (w : Fin N → ℕ) (tag : Fin N → TargetTag)
    (pos : (b : Fin N) → Fin (w b) → ℕ) (outer : List Tally) (dir : List Tally)
    (lift : ℕ → ℕ) (subset : Fin M → Fin N) (side : Bool) (stage : ℕ)
    (ho : ∀ k ∈ outer, Iter.pick [] (dir,k) = tally (lift k.length))
    (hi : ∀ (b : Fin M) (k : Fin (w (subset b))),
      Iter.pick [] (dir,tally (pos (subset b) k)) = tally (lift (pos (subset b) k))) :
    relocate (Benes.makePlan side stage outer w tag pos,dir,List.ofFn (fun b => tally (subset b).val)) =
      Benes.makePlan side stage (outer.map (fun k => tally (lift k.length)))
        (w ∘ subset) (tag ∘ subset) (fun b k => lift (pos (subset b) k)) := by
  have external : remapPositions (dir,outer) = outer.map (fun k => tally (lift k.length)) :=
    List.map_congr_left ho
  simp only [relocate, Benes.makePlan,external,polyPush,List.map_ofFn]
  congr 2
  funext b
  simp only [Function.comp_apply, Iter.entry, remapBlock,remapPositions,polyPush,List.map_ofFn]
  exact congrArg (fun f => (tag (subset b),tally (w (subset b)),List.ofFn f)) (funext (hi b))

end CRTTable

end NearSquareRoot
end Computability
end OAI
