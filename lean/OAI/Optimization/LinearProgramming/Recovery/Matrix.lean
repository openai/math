import OAI.Optimization.LinearProgramming.Recovery.Presentation
import OAI.Optimization.LinearProgramming.Elimination.Solve

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

open Matrix
open scoped Matrix

namespace Presentation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- The fallback gives a total routine on arbitrary input presentations. It is unreachable
on an accepting restriction that has a witness positive at the anchor. -/
def generator (i : Fin n) (u : Presentation K n) : Fin n → K :=
  match Elimination.solve (u.anchorMatrix i) (anchorRhs u.rows) with
  | none => 0
  | some z => Elimination.tabulateVec (u.output *ᵥ z)

theorem generator_spec (u : Presentation K n) (i : Fin n)
    (h : ∃ x ∈ u.denote, 0 ≤ x ∧ 0 < x i) :
    generator i u ∈ u.denote ∧ generator i u i = 1 := by
  obtain ⟨x,⟨z,hz,hx⟩,_,hi⟩ := h
  change u.equations *ᵥ z = 0 at hz
  change u.output *ᵥ z = x at hx
  have hex : ∃ y, u.anchorMatrix i *ᵥ y = anchorRhs u.rows := by
    refine ⟨(x i)⁻¹ • z, (anchor_equations u i _).mpr ⟨?_, ?_⟩⟩
    · simp [Matrix.mulVec_smul, hx, hi.ne']
    · simp [Matrix.mulVec_smul, hz]
  obtain ⟨y,hy⟩ := Elimination.solve_complete _ _ hex
  obtain ⟨hanchor,hker⟩ := (anchor_equations u i y).mp (Elimination.solve_sound _ _ _ hy)
  simpa only [generator,hy,Elimination.tabulateVec_eq] using
    And.intro ((mem_denote u _).mpr ⟨y,hker,rfl⟩) hanchor

end Presentation

open Presentation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n t : ℕ}

/-- Concrete search, with a Boolean marked-coordinate decision as its only oracle.
The two initial representations are the column span of `B` and the kernel of `Bᵀ`. -/
def recoverColumns (decide : Presentation K n → Bool) (B : Matrix (Fin n) (Fin t) K) (i : Fin n) :=
  recoverWitness decide (fun _ => fromKernel Bᵀ) restrict (generator i) (fromColumns B) i

theorem recoverColumns_spec (decide : Presentation K n → Bool) (B : Matrix (Fin n) (Fin t) K) (i : Fin n)
    (oracle : ∀ r, decide r = true ↔ ∃ x ∈ r.denote, 0 ≤ x ∧ 0 < x i) :
    let r := recoverColumns decide B i
    let side := if r.primal then fromColumns B else fromKernel Bᵀ
    r.queries.length = n ∧ r.primal = decide (fromColumns B) ∧
    Module.finrank K (side.restrict r.allowed).denote = 1 ∧ r.point ∈ side.denote ∧
    0 ≤ r.point ∧ r.point i = 1 ∧ (∀ j, j ∉ r.allowed → r.point j = 0) := by
  apply recoverWitness_spec (denote := denote) (dual := transpose_kernel B) (cut := restrict_spec)
    (oracle := oracle)
  intro u _ h
  obtain ⟨hg,hi⟩ := generator_spec u i h
  refine ⟨hg,fun zero => one_ne_zero (α := K) ?_⟩
  rw [← hi,zero]
  rfl

end Recovery
end LinearProgramming
end Optimization
end OAI
