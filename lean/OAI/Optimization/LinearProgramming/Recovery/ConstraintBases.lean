import OAI.Optimization.LinearProgramming.Geometry.GramAlgorithm
import OAI.Optimization.LinearProgramming.Geometry.RationalSubspace
import OAI.Optimization.LinearProgramming.Recovery.Kernel

/-! The support oracle's fixed-matrix implementation needs only an independent row scan,
Gram projection, subtraction from the identity, and a second row scan. This interface
allows any packing of the selected independent rows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

open Matrix Submodule Module Presentation
open _root_.OAI.Optimization.LinearProgramming.Geometry
open scoped Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r s n q : ℕ}

abbrev rowSpace (B : Matrix (Fin r) (Fin n) K) := span K (Set.range B.row)

/-- The output matrix selected by the normal row-basis scan may use any deterministic
order, provided this exact independence and spanning statement holds. -/
structure PacksRows (B : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K) : Prop where
  independent : LinearIndependent K E.row
  span_eq : rowSpace E = rowSpace B

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem rowSpace_eq_range (B : Matrix (Fin r) (Fin n) K) : rowSpace B = LinearMap.range Bᵀ.mulVecLin := by
  rw [Matrix.range_mulVecLin]; rfl

theorem selected_rows_pack (B : Matrix (Fin r) (Fin n) K) : PacksRows B (basisRows Bᵀ) :=
  ⟨basisRows_independent _,(basisRows_span _).trans (rowSpace_eq_range B).symm⟩

/-- The uniform residual writer implements this row-major matrix using the exact Gram
program's output. All computations use the field of the original input. -/
def kernelRows (E : Matrix (Fin s) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  tabulateRect (1 - computeGramProjector E)

omit [IsStrictOrderedRing K] in
@[simp] theorem kernelRows_eq (E : Matrix (Fin s) (Fin n) K) : kernelRows E = 1-rowGramProjector E := by
  simp [kernelRows]

theorem kernelRows_span (E : Matrix (Fin s) (Fin n) K) (hE : LinearIndependent K E.row) :
    rowSpace (kernelRows E) = LinearMap.ker E.mulVecLin := by
  rw [rowSpace_eq_range,kernelRows_eq,Matrix.transpose_sub,Matrix.transpose_one,rowGramProjector_transpose]
  have fix := congrArg Matrix.transpose (rowGramProjector_fix_rows E (gram_det_isUnit_of_independent_rows E hE))
  have fix' : E * rowGramProjector E = E := by simpa [rowGramProjector_transpose] using fix
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    change E *ᵥ ((1-rowGramProjector E) *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec,Matrix.mul_sub,Matrix.mul_one,fix',sub_self,Matrix.zero_mulVec]
  · intro x hx
    change E *ᵥ x = 0 at hx
    refine ⟨x,?_⟩
    change (1-rowGramProjector E) *ᵥ x = x
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,rowGramProjector,← Matrix.mulVec_mulVec,hx,Matrix.mulVec_zero,sub_zero]

/-- Starting from *any* matrix of equations C, these operations provide every premise of
the complementary-row oracle, and its positive sign refers to precisely `ker C`. -/
theorem kernelPair_spec (C : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K)
    (D : Matrix (Fin q) (Fin n) K) (he : PacksRows C E) (hd : PacksRows (kernelRows E) D) :
    LinearIndependent K D.row ∧ LinearIndependent K E.row ∧ D * Eᵀ=0 ∧ q+s=n ∧
      rowSpace D = LinearMap.ker C.mulVecLin := by
  have hker : LinearMap.ker E.mulVecLin = LinearMap.ker C.mulVecLin := by
    rw [← rowSpan_orthogonalBilin_eq_ker,← rowSpan_orthogonalBilin_eq_ker]
    exact congrArg (fun W : Submodule K (Fin n → K) => W.orthogonalBilin (dotProductBilin K K)) he.span_eq
  have hD := hd.span_eq.trans (kernelRows_span E he.independent)
  refine ⟨hd.independent,he.independent,?_,?_,hD.trans hker⟩
  · ext i j
    have h : D i ∈ rowSpace D := subset_span ⟨i,rfl⟩
    rw [hD] at h
    have z := congrFun (LinearMap.mem_ker.mp h) j
    change D i ⬝ᵥ E j = 0
    exact (dotProduct_comm _ _).trans z
  · have hn := E.mulVecLin.finrank_range_add_finrank_ker
    change E.rank + Module.finrank K (LinearMap.ker E.mulVecLin) = _ at hn
    rw [← hD, ← Matrix.rank_eq_finrank_span_row,hd.independent.rank_matrix,he.independent.rank_matrix,
      Module.finrank_fintype_fun_eq_card] at hn
    simpa [Nat.add_comm] using hn

/-- Append constraint rows from the fixed identity table only on discarded coordinates.
All rows occur in their original coordinate positions, even if their entries are zero. -/
def maskedEquations (E : Matrix (Fin s) (Fin n) K) (S : Finset (Fin n)) : Matrix (Fin (s+n)) (Fin n) K :=
  ((fromKernel E).restrict S).equations

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem maskedEquations_ker (E : Matrix (Fin s) (Fin n) K) (S : Finset (Fin n)) (x : Fin n → K) :
    x ∈ LinearMap.ker (maskedEquations E S).mulVecLin ↔ x ∈ LinearMap.ker E.mulVecLin ∧ ∀ j, j ∉ S → x j = 0 := by
  change ((fromKernel E).restrict S).equations *ᵥ x = 0 ↔ E *ᵥ x = 0 ∧ _
  have hI : (fromKernel E).output *ᵥ x = x := Matrix.one_mulVec x
  have eqs := (fromKernel E).restrict_equations S x
  constructor
  · intro h
    obtain ⟨e,z⟩ := eqs.mp h
    exact ⟨e,fun j hj => (congrFun hI j).symm.trans (z j hj)⟩
  · rintro ⟨e,z⟩
    exact eqs.mpr ⟨e,fun j hj => (congrFun hI j).trans (z j hj)⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem maskedEquations_present (side : Presentation K n) (E : Matrix (Fin s) (Fin n) K)
    (hE : LinearMap.ker E.mulVecLin = side.denote) (S : Finset (Fin n)) :
    LinearMap.ker (maskedEquations E S).mulVecLin = (side.restrict S).denote := by
  ext x
  rw [maskedEquations_ker,hE,restrict_spec side S x]

end Recovery
end LinearProgramming
end Optimization
end OAI
