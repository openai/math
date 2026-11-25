import OAI.Hierarchy.TaggedRadixScatter
import OAI.Hierarchy.TaggedSortRelation
import OAI.Hierarchy.TaggedPassState
import OAI.Hierarchy.TaggedPassShell
import OAI.Hierarchy.TaggedLocalDestination

namespace OAI
/-! # Evaluation of a full packed radix pass with three tagged calls -/

namespace Hierarchy.Tagged.Radix.PassShape
open ThreeFlat Routing SortNetwork RadixStage
open SortedBlock CorrectionFrame
open scoped Classical
noncomputable section

variable {w d : ℕ} (s : PassShape) (dummy : Fin w → Bool) (real isDummy : Fin w) (digit : Fin s.digitBits → Fin w)

private theorem sortData_ok {l k w : ℕ} (F : Type*) [CommSemiring F] (key : Fin k → Fin w) :
    Computes (SortRelation.shell (h := l) F key) (coeff F l (l+w)) (sortData key) := by
  intro x y
  have sorted := SortRelation.eval F key (unwrap x) y
  simp only [contract,row,pack_unwrap,sortData,stable] at sorted ⊢
  first
  | exact sorted
  | refine Eq.trans ?_ sorted
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext hole
    simp

private theorem liftOn {F : Type*} {I O H : Type} [CommSemiring F] [Fintype I] [Fintype O] [Fintype H]
    {N : Network F I O H} {φ : (H → Bool) → F} {f : (I → Bool) → O → Bool}
    (g : (I → Bool) → Prop) (ok : Computes N φ f) : ComputesOn N φ g f := fun x _ y => ok x y

/-- Exact evaluation with a cut-open parallel local sort, parallel alignment,
and wide sort. Their weights are contracted directly into the physical shell. -/
theorem computes (F : Type*) [CommSemiring F] (space : s.packBits+2 ≤ s.digitBits)
    (blank : dummy real = false) (comp : dummy isDummy = !(dummy real)) :
    ComputesOn (s.network F dummy real isDummy digit) (weight F s w)
      (shapeFlags s.rows real isDummy) (s.run dummy real isDummy digit) := by
  let good : (s.LocalData w → Bool) → Prop := fun x => ∀ b, AlignedInput digit real (unwrap (fun i => x (b,i)))
  have sort := parallel_computes (fun _ : Fin s.blocks => SortRelation.shell (h := s.localBits) F (maskedDigit digit isDummy))
    (coeff F s.localBits (s.localBits+w)) (fun _ => sortData (maskedDigit digit isDummy)) (fun _ => sortData_ok F _)
  have align_ok := parallel_computesOn (fun _ : Fin s.blocks => AlignShell.shell (AlignRows.network (j := s.packBits) (t := s.upperBits) F real digit))
    (coeff F s.localBits w) (fun _ => alignData digit real) (fun _ x => AlignedInput digit real (unwrap x)) (by
      intro _ x ok y
      have placed := eval_align digit real (unwrap x) F ok y
      simp only [pack_unwrap,localBits,alignData] at placed ⊢
      by_cases same : y = SortNetwork.pack (align digit real (unwrap x))
      all_goals simp only [same,ite_true,ite_false] at placed ⊢
      all_goals first
        | exact placed)
  have first := (scatter_computes (F := F) (s.enter dummy)).seq sort
  have lead := (liftOn (shapeFlags s.rows real isDummy) first).seq align_ok (fun x valid b => local_ok s dummy real isDummy digit space blank comp x valid b)
  have middle := lead.seq (liftOn (fun _ => True) (scatter_computes (F := F) (s.wideInput dummy))) (fun _ _ => trivial)
  have wide := middle.seq (liftOn (fun _ => True) (sortData_ok F (s.wideDigit digit isDummy))) (fun _ _ => trivial)
  exact wide.seq (liftOn (fun _ => True) (scatter_computes (F := F) s.leave)) (fun _ _ => trivial)

end
end Hierarchy.Tagged.Radix.PassShape

end OAI
