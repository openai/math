import OAI.Optimization.LinearProgramming.Recovery.Witness

/-! Section 2.3 over explicit finite matrices. A presentation yields all `B z` with
`A z = 0`. To set a coordinate of `B z` to zero, use that row of `B` as an additional
homogeneous equation. To recover the final oriented generator, set its anchor to one
and solve one ordinary rectangular system with `Elimination.solve`. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

open Matrix
open scoped Matrix

/-- A subspace presented as the image of a kernel, with a visible ambient dimension. -/
structure Presentation (K : Type*) (n : ℕ) where
  nVars : ℕ
  rows : ℕ
  equations : Matrix (Fin rows) (Fin nVars) K
  output : Matrix (Fin n) (Fin nVars) K

namespace Presentation

variable {K : Type*} [Field K] {n t : ℕ}

def denote (u : Presentation K n) : Submodule K (Fin n → K) :=
  (LinearMap.ker u.equations.mulVecLin).map u.output.mulVecLin

@[simp] theorem mem_denote (u : Presentation K n) (x : Fin n → K) : x ∈ u.denote ↔
    ∃ z, u.equations *ᵥ z = 0 ∧ u.output *ᵥ z = x := Iff.rfl

/-- Rows for surviving coordinates are zero. All other added rows enforce that output
coordinate's vanishing. Matrix sizes are independent of the earlier deletion attempts. -/
def restrict (u : Presentation K n) (s : Finset (Fin n)) : Presentation K n :=
  { u with rows := u.rows + n
           equations := Fin.append (fun r j => u.equations r j) (fun j => if j ∈ s then 0 else u.output j) }

theorem restrict_equations (u : Presentation K n) (s : Finset (Fin n)) (z : Fin u.nVars → K) :
    (u.restrict s).equations *ᵥ z = 0 ↔
      u.equations *ᵥ z = 0 ∧ ∀ j, j ∉ s → (u.output *ᵥ z) j = 0 := by
  have left (k : Fin u.rows) : ((u.restrict s).equations *ᵥ z) (Fin.castAdd n k) = (u.equations *ᵥ z) k := by
    change Fin.append (fun r j => u.equations r j) (fun j => if j ∈ s then 0 else u.output j) (Fin.castAdd n k) ⬝ᵥ z = u.equations k ⬝ᵥ z
    rw [Fin.append_left]
  have right (k : Fin n) : ((u.restrict s).equations *ᵥ z) (Fin.natAdd u.rows k) =
      if k ∈ s then (0 : K) else (u.output *ᵥ z) k := by
    change Fin.append (fun r j => u.equations r j) (fun j => if j ∈ s then 0 else u.output j) (Fin.natAdd u.rows k) ⬝ᵥ z = _
    rw [Fin.append_right]
    by_cases hk : k ∈ s
    · simp [hk]
    · simp [hk,Matrix.mulVec]
  constructor
  · intro h
    constructor
    · exact funext fun k => (left k).symm.trans (congrFun h _)
    · intro j hj
      have h' := congrFun h (Fin.natAdd u.rows j)
      rw [right j, ite_eq_right hj] at h'
      exact h'
  · rintro ⟨h,zout⟩
    funext r
    refine Fin.addCases (fun k => (left k).trans (congrFun h _)) (fun k => ?_) r
    change ((u.restrict s).equations *ᵥ z) (Fin.natAdd u.rows k) = 0
    rw [right]
    split_ifs with hk
    · rfl
    · exact zout k hk

theorem restrict_spec : Restricts (denote (K := K) (n := n)) restrict := by
  intro u s x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h,hs⟩ := (restrict_equations u s z).mp hz
    exact ⟨⟨z,h,rfl⟩,hs⟩
  · rintro ⟨⟨z,h,rfl⟩,hz⟩
    exact ⟨z,(restrict_equations u s z).mpr ⟨h,hz⟩,rfl⟩

def anchorMatrix (u : Presentation K n) (i : Fin n) : Matrix (Fin (u.rows+1)) (Fin u.nVars) K :=
  Fin.cons (u.output i) u.equations

def anchorRhs (r : ℕ) : Fin (r+1) → K := Fin.cons 1 0

theorem anchor_equations (u : Presentation K n) (i : Fin n) (z : Fin u.nVars → K) :
    u.anchorMatrix i *ᵥ z = anchorRhs u.rows ↔
      (u.output *ᵥ z) i = 1 ∧ u.equations *ᵥ z = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, funext fun j => congrFun h j.succ⟩
  · rintro ⟨hi,h⟩
    exact funext fun j => Fin.cases hi (fun k => congrFun h k) j

def fromColumns (B : Matrix (Fin n) (Fin t) K) : Presentation K n :=
  ⟨t, 0, 0, B⟩

def fromKernel {r : ℕ} (B : Matrix (Fin r) (Fin n) K) : Presentation K n :=
  ⟨n, r, B, 1⟩

@[simp] theorem denote_columns (B : Matrix (Fin n) (Fin t) K) :
    (fromColumns B).denote = LinearMap.range B.mulVecLin := by
  ext x
  change (∃ z : Fin t → K, (0 : Matrix (Fin 0) (Fin t) K) *ᵥ z = 0 ∧ B *ᵥ z = x) ↔ _
  simp only [Matrix.zero_mulVec, true_and]
  rfl

@[simp] theorem denote_kernel {r : ℕ} (B : Matrix (Fin r) (Fin n) K) :
    (fromKernel B).denote = LinearMap.ker B.mulVecLin := by
  ext x
  change (∃ z, B *ᵥ z = 0 ∧ (1 : Matrix (Fin n) (Fin n) K) *ᵥ z = x) ↔ B *ᵥ x = 0
  simp

/-- The transpose equations present the dual of an explicitly generated subspace. -/
theorem transpose_kernel (B : Matrix (Fin n) (Fin t) K) :
    (fromKernel Bᵀ).denote = (fromColumns B).denote.orthogonalBilin (dotProductBilin K K) := by
  rw [denote_kernel, denote_columns]
  ext x
  change Bᵀ *ᵥ x = 0 ↔ ∀ y ∈ LinearMap.range B.mulVecLin, y ⬝ᵥ x = 0
  constructor
  · rintro h _ ⟨z,rfl⟩
    change (B *ᵥ z) ⬝ᵥ x = 0
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h, zero_dotProduct]
  · intro h
    apply dotProduct_eq_zero
    intro z
    have hz := h (B *ᵥ z) ⟨z,rfl⟩
    rwa [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at hz

end Presentation

end Recovery
end LinearProgramming
end Optimization
end OAI
