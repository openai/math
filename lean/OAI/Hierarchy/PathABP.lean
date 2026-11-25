import OAI.Hierarchy.ChainABP
import OAI.Hierarchy.GraphFamilyBounds
import OAI.Hierarchy.PathContractionDP

namespace OAI
/-! # Polynomial-size branching programs for path contractions -/

namespace Hierarchy

open Computability.VPVNP IncidenceGraph
open scoped BigOperators
noncomputable section

/-- At length `n` the program has one layer per internal vertex and at most
`n` states in a layer. Each edge reads a single vertex-table variable. -/
theorem path_hasABP (F : Type*) [Field F] (n : ℕ) :
    HasABP (3 * (n + 1)^3) ((path n).contraction F n) := by
  classical
  match n with
  | 0 =>
    rw [PathDP.contraction_zero]
    exact ⟨⟨1,.source,0⟩,rfl,by change (1 : ℕ) ≤ 3; decide⟩
  | 1 =>
    rw [PathDP.contraction_one]
    let g : ABP F ((path 1).TableVar 1) :=
      ⟨2, Rows.source.snoc [(0, Affine.ofVariable (PathDP.single 1))], Fin.last 1⟩
    refine ⟨g,?_,?_⟩
    · simp only [g,ABP.polynomial,Rows.values,Fin.lastCases_last,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,one_mul,add_zero,Affine.polynomial_ofVariable]
    · change (3 : ℕ) ≤ 3 * (1 + 1)^3
      decide
  | m+2 =>
    let q := m+2
    obtain ⟨g,value,size⟩ := ChainProduct.hasABP m
      (fun a => Affine.ofVariable (F := F) (PathDP.left m q a))
      (fun a => Affine.ofVariable (F := F) (PathDP.right m q a))
      (fun i a b => Affine.ofVariable (F := F) (PathDP.middle m q i a b))
    refine ⟨g,?_,size.trans ?_⟩
    · rw [PathDP.contraction_eq]
      simpa only [Affine.polynomial_ofVariable] using value
    · dsimp only [q]
      nlinarith only [Nat.zero_le m, Nat.zero_le (m^2), Nat.zero_le (m^3)]

/-- The actual vertex-table contractions of paths, with edge dimension equal
to the family index, belong to VBP over every field. -/
theorem path_isVBP (F : Type*) [Field F] : IsVBP (contractionFamily F path) := by
  classical
  have order : PolynomiallyBounded (fun n => Fintype.card (path n).V) := by
    simpa only [path_order] using PolynomiallyBounded.id
  have poly := contractionFamily_pFamily F path order ⟨2,path_degree_le⟩
  choose g value size using path_hasABP F
  refine ⟨poly,g,value,?_⟩
  exact ((PolynomiallyBounded.const 3).mul
    ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).pow 3)).of_le size


end
end Hierarchy

end OAI
