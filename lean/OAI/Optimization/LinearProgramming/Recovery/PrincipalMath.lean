import OAI.Optimization.LinearProgramming.Recovery.EquationWitness
import OAI.Optimization.LinearProgramming.Recovery.ConstraintBases

/-! Relate the results of the physical marked tests to the concrete normalized
witness. The truth predicate below appears only in the specification and proofs. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal
open Matrix Submodule Geometry Presentation
open scoped Matrix

variable {K : Type*} [Field K] [LinearOrder K]

noncomputable def yes {n : ℕ} (i : Fin n) (u : Presentation K n) : Bool := by
  classical
  exact decide (∃z∈u.denote,0 ≤ z ∧ 0 < z i)

theorem yes_correct {n : ℕ} (i : Fin n) (u : Presentation K n) : yes i u=true ↔ ∃z∈u.denote,0 ≤ z ∧ 0 < z i := by
  classical
  simp [yes]

variable {m d h k s : ℕ}

noncomputable def ref (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) := recoverColumns (yes 0) (slackColumns A b) 0

def side (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (positive : Bool) := if positive then primalPresentation A b else dualPresentation A b

noncomputable def restriction (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (positive : Bool) (S : Finset (Fin (m+1))) :=
  yes 0 ((side A b positive).restrict S)

theorem allowed (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) :
    (ref A b).allowed=(deleteCoordinates (restriction A b (ref A b).primal) ((List.finRange (m+1)).erase 0) Finset.univ).1 := rfl

theorem initial_answer (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (F : Matrix (Fin k) (Fin (m+1)) K)
    (basis : PacksRows (slackColumns A b)ᵀ F) : (ref A b).primal=true ↔ ∃z∈rowSpace F,0 ≤ z ∧ 0 < z 0 := by
  change yes 0 (fromColumns (slackColumns A b))=true ↔ _
  rw [yes_correct,denote_columns,basis.span_eq,rowSpace_eq_range,Matrix.transpose_transpose]

variable [IsStrictOrderedRing K]

theorem opposite_spaces (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (F : Matrix (Fin k) (Fin (m+1)) K)
    (R : Matrix (Fin s) (Fin (m+1)) K) (hf : PacksRows (slackColumns A b)ᵀ F) (hr : PacksRows (kernelRows F) R) :
    LinearMap.ker R.mulVecLin=(side A b true).denote ∧ LinearMap.ker F.mulVecLin=(side A b false).denote := by
  obtain ⟨r,f,orth,dim,spaceR⟩:=kernelPair_spec (slackColumns A b)ᵀ F R hf hr
  have fspace : rowSpace F=(primalPresentation A b).denote:=by
    rw [hf.span_eq,rowSpace_eq_range,Matrix.transpose_transpose,primalPresentation,denote_columns]
  have dual : LinearMap.ker F.mulVecLin=rowSpace R := (hr.span_eq.trans (kernelRows_span F hf.independent)).symm
  have primal : LinearMap.ker R.mulVecLin=rowSpace F:=by
    rw [←rowSpan_orthogonalBilin_eq_ker]
    exact (complementary_rowSpan R F r f orth dim).symm
  exact ⟨primal.trans fspace,dual.trans (spaceR.trans (denote_kernel _).symm)⟩

omit [IsStrictOrderedRing K] in
theorem restriction_correct (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (positive : Bool)
    (E : Matrix (Fin h) (Fin (m+1)) K) (eqs : LinearMap.ker E.mulVecLin=(side A b positive).denote) (S : Finset (Fin (m+1))) :
    restriction A b positive S=true ↔ ∃z∈LinearMap.ker (maskedEquations E S).mulVecLin,0 ≤ z ∧ 0 < z 0 := by
  rw [restriction,yes_correct,maskedEquations_present _ E eqs S]

theorem normalized_solution (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (E : Matrix (Fin h) (Fin (m+1)) K)
    (eqs : LinearMap.ker E.mulVecLin=(side A b (ref A b).primal).denote) :
    Elimination.fixedSolve (normalizedSystem (maskedEquations E (ref A b).allowed) 0) (anchorRhs (h+(m+1)))=some (ref A b).point := by
  exact fixedSolve_marked_point (yes 0) (slackColumns A b) 0 (yes_correct 0) _ (maskedEquations_present _ E eqs _)

theorem primal_point (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (hp : (ref A b).primal=true) :
    ∃ x,Elimination.fixedSolve A (b-Fin.tail (ref A b).point)=some x ∧ Feasible A b x := by
  obtain ⟨_,_,_,mem,nonneg,norm,_⟩:=recoverColumns_spec (yes 0) (slackColumns A b) 0 (yes_correct 0)
  change (ref A b).point ∈ (side A b (ref A b).primal).denote at mem
  rw [hp] at mem
  obtain ⟨x,sol,feas⟩:=decodePrimal A b (ref A b).point mem nonneg norm
  exact ⟨x,(Elimination.fixedSolve_eq_solve _ _).trans sol,feas⟩

theorem dual_point (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (hp : (ref A b).primal=false) :
    Certificate A b (Fin.tail (ref A b).point) ∧ b ⬝ᵥ Fin.tail (ref A b).point=-1 := by
  obtain ⟨_,_,rank,mem,nonneg,norm,supported⟩:=recoverColumns_spec (yes 0) (slackColumns A b) 0 (yes_correct 0)
  change (ref A b).point ∈ (side A b (ref A b).primal).denote at mem
  change Module.finrank K ((side A b (ref A b).primal).restrict (ref A b).allowed).denote=1 at rank
  rw [hp] at mem rank
  obtain ⟨ny,zero,negative,size⟩:=decodeDual A b (ref A b).point (ref A b).allowed mem nonneg norm supported rank
  exact ⟨⟨ny,zero,by rw [negative];norm_num,size⟩,negative⟩

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
