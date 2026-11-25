import OAI.Optimization.LinearProgramming.Recovery.LP
import OAI.Optimization.LinearProgramming.Elimination.SolveEquiv

/-! The normal solver recovers the marked vector directly from the equations of its
final support. One row enforces the anchor value one. The one-dimensionality proved
by support deletion makes its vector exactly the one used by the high-level decoder. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

open Matrix Presentation
open scoped Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n t m d k : ℕ}

/-- Dense input to the native rectangular solve, with the marked equation first. -/
def normalizedSystem (C : Matrix (Fin k) (Fin n) K) (i : Fin n) : Matrix (Fin (k+1)) (Fin n) K :=
  Fin.cons (fun j => if j=i then 1 else 0) C

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem normalizedSystem_mulVec (C : Matrix (Fin k) (Fin n) K) (i : Fin n) (z : Fin n → K) :
    normalizedSystem C i *ᵥ z = anchorRhs k ↔ z i=1 ∧ C *ᵥ z=0 := by
  have top : (normalizedSystem C i *ᵥ z) 0 = z i := by
    change (∑ j : Fin n, (if j=i then (1:K) else 0)*z j) = _
    simp [ite_mul]
  have rows (j : Fin k) : (normalizedSystem C i *ᵥ z) j.succ=(C*ᵥz) j := rfl
  constructor
  · intro h
    refine ⟨top.symm.trans (congrFun h 0),?_⟩
    funext j; exact (rows j).symm.trans (congrFun h j.succ)
  · rintro ⟨hi,hz⟩
    funext j
    exact Fin.cases (top.trans hi) (fun a=>(rows a).trans (congrFun hz a)) j

/-- Any equation matrix cutting out the final winning line yields precisely the same
normalized vector, including for a negative certificate and nonunique original LP points. -/
theorem fixedSolve_marked_point (decide : Presentation K n → Bool) (B : Matrix (Fin n) (Fin t) K)
    (i : Fin n) (oracle : ∀ u,decide u=true ↔ ∃ x∈u.denote, 0 ≤ x ∧ 0 < x i)
    (C : Matrix (Fin k) (Fin n) K) :
    let r := recoverColumns decide B i
    let side := if r.primal then fromColumns B else fromKernel Bᵀ
    LinearMap.ker C.mulVecLin = (side.restrict r.allowed).denote →
    Elimination.fixedSolve (normalizedSystem C i) (anchorRhs k) = some r.point := by
  intro r side hker
  obtain ⟨_,_,line,mem,_,hi,off⟩ := recoverColumns_spec decide B i oracle
  have point : r.point ∈ (side.restrict r.allowed).denote := (restrict_spec side r.allowed _).mpr ⟨mem,off⟩
  have ceq : C *ᵥ r.point=0 := LinearMap.mem_ker.mp (hker.symm ▸ point)
  obtain ⟨z,hz⟩ := Elimination.fixedSolve_complete (normalizedSystem C i) (anchorRhs k)
    ⟨r.point,(normalizedSystem_mulVec C i _).mpr ⟨hi,ceq⟩⟩
  obtain ⟨zi,z0⟩ := (normalizedSystem_mulVec C i z).mp (Elimination.fixedSolve_sound _ _ _ hz)
  have zm : z ∈ (side.restrict r.allowed).denote := hker ▸ (LinearMap.mem_ker.mpr z0)
  exact hz.trans (congrArg some (marked_line_unique _ i line zm point zi hi))

/-- Actual final native routine takes just the orientation flag, constraint array and
original A,b. It performs one anchored rectangular solve and a further solve in the primal case. -/
def finishByEquations (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K)
    (C : Matrix (Fin k) (Fin (m+1)) K) (primal : Bool) : Option (Sum (Fin d→K) (Fin m→K)) := do
  let w ← Elimination.fixedSolve (normalizedSystem C 0) (anchorRhs k)
  if primal then return .inl (← Elimination.fixedSolve A (b-Fin.tail w))
  else return .inr (Fin.tail w)

theorem finishByEquations_eq (decide : Presentation K (m+1) → Bool) (A : Matrix (Fin m) (Fin d) K)
    (b : Fin m→K) (oracle : ∀ u,decide u=true ↔ ∃ x∈u.denote, 0 ≤ x ∧ 0 < x 0)
    (C : Matrix (Fin k) (Fin (m+1)) K) :
    let r := recoverColumns decide (slackColumns A b) 0
    let side := if r.primal then primalPresentation A b else dualPresentation A b
    LinearMap.ker C.mulVecLin = (side.restrict r.allowed).denote →
    finishByEquations A b C r.primal = (solveLP decide A b).value := by
  intro r _side hker
  have hz : Elimination.fixedSolve (normalizedSystem C 0) (anchorRhs k) = some r.point :=
    fixedSolve_marked_point decide (slackColumns A b) 0 oracle C hker
  change finishByEquations A b C r.primal =
    (if r.primal then (Elimination.solve A (b-Fin.tail r.point)).map Sum.inl
     else some (Sum.inr (Fin.tail r.point)))
  unfold finishByEquations
  rw [hz]
  change (if r.primal then
      (Elimination.fixedSolve A (b-Fin.tail r.point)).bind (fun x => some (Sum.inl x))
    else some (Sum.inr (Fin.tail r.point))) = _
  rw [Elimination.fixedSolve_eq_solve]
  cases r.primal <;> cases Elimination.solve A (b-Fin.tail r.point) <;> rfl

end Recovery
end LinearProgramming
end Optimization
end OAI
