import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! # Block pivots in a quotient of independent lists

Reading the coordinate blocks of a single row space in order produces pivots
whose dimensions telescope. A rank correction can involve every block.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Module LinearMap
variable {K W V : Type*} [Field K] [AddCommGroup W] [Module K W]
  [AddCommGroup V] [Module K V] [FiniteDimensional K W]

/-- Row vectors whose first `t` blocks vanish. -/
def blockKernel (f : ℕ → W →ₗ[K] V) : ℕ → Submodule K W
  | 0 => ⊤
  | t + 1 => blockKernel f t ⊓ LinearMap.ker (f t)

/-- The pivot space in block `t` after all earlier blocks have been eliminated. -/
def blockPivots (f : ℕ → W →ₗ[K] V) (t : ℕ) : Submodule K V :=
  (blockKernel f t).map (f t)

omit [FiniteDimensional K W] in
theorem mem_blockKernel_iff (f : ℕ → W →ₗ[K] V) (t : ℕ) (x : W) :
    x ∈ blockKernel f t ↔ ∀ j < t, f j x = 0 := by
  induction t with
  | zero => simp [blockKernel]
  | succ t ih =>
    simp only [blockKernel, Submodule.mem_inf, LinearMap.mem_ker, ih]
    exact ⟨fun ⟨h, hlast⟩ j hj => (lt_or_eq_of_le (Nat.le_of_lt_succ hj)).elim
      (h j) (fun e => e ▸ hlast), fun h => ⟨fun j hj => h j (by omega), h t (by omega)⟩⟩

theorem blockPivots_finrank_step (f : ℕ → W →ₗ[K] V) (t : ℕ) :
    finrank K (blockPivots f t) + finrank K (blockKernel f (t + 1)) =
      finrank K (blockKernel f t) := by
  let L := blockKernel f t
  let g := (f t).domRestrict L
  have he : (LinearMap.ker g).map L.subtype = blockKernel f (t + 1) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hz⟩
      exact ⟨⟨x, hx⟩, hz, rfl⟩
  have hk := (L.equivSubtypeMap (LinearMap.ker g)).finrank_eq
  rw [he] at hk
  have hr : LinearMap.range g = blockPivots f t := LinearMap.range_domRestrict ..
  rw [← hr, ← hk]
  exact g.finrank_range_add_finrank_ker

theorem sum_blockPivots_finrank (f : ℕ → W →ₗ[K] V) (t : ℕ) :
    (∑ j ∈ Finset.range t, finrank K (blockPivots f j)) + finrank K (blockKernel f t) =
      finrank K W := by
  induction t with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add, blockKernel]
            exact (Submodule.topEquiv (R := K) (M := W)).finrank_eq
  | succ t ih => rw [Finset.sum_range_succ, Nat.add_assoc, blockPivots_finrank_step, ih]

/-- At a faithful list of coordinate blocks the pivot counts use every row dimension. -/
theorem sum_blockPivots_finrank_of_separating (f : ℕ → W →ₗ[K] V) (t : ℕ)
    (h : ∀ x : W, (∀ j < t, f j x = 0) → x = 0) :
    ∑ j ∈ Finset.range t, finrank K (blockPivots f j) = finrank K W := by
  have hz : blockKernel f t = ⊥ := le_bot_iff.mp fun x hx =>
    (Submodule.mem_bot K).mpr (h x ((mem_blockKernel_iff f t x).mp hx))
  have hsum := sum_blockPivots_finrank f t
  rw [hz, finrank_bot, Nat.add_zero] at hsum
  exact hsum

/-- View a row annihilating the rank error as a list of coordinate blocks.
Blocks beyond the list are zero. -/
def annihilatorBlock {n J : ℕ} {C : Type*} [Fintype C]
    (B : Matrix (Fin n × Fin J) C K) (j : ℕ) :
    (LinearMap.ker B.transpose.mulVecLin) →ₗ[K] (Fin n → K) :=
  if hj : j < J then
    { toFun := fun x i => x.val (i, ⟨j, hj⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  else 0

/-- For a shared rank correction the missing block pivots total exactly its rank.
The error may have entries in arbitrary off-diagonal blocks. -/
theorem sum_annihilator_pivots_add_rank {n J : ℕ} {C : Type*} [Fintype C]
    (B : Matrix (Fin n × Fin J) C K) :
    (∑ j ∈ Finset.range J, finrank K (blockPivots (annihilatorBlock B) j)) + B.rank =
      J*n := by
  have sep (x : LinearMap.ker B.transpose.mulVecLin)
      (hx : ∀ j < J, annihilatorBlock B j x = 0) : x = 0 := by
    apply Subtype.ext
    funext ⟨i,j⟩
    have hv := congrFun (hx j.val j.isLt) i
    simpa [annihilatorBlock, j.isLt] using hv
  rw [sum_blockPivots_finrank_of_separating _ _ sep, Nat.add_comm, ← Matrix.rank_transpose B]
  have rankNull := B.transpose.mulVecLin.finrank_range_add_finrank_ker
  simpa [Matrix.rank, Module.finrank_pi, Nat.mul_comm] using rankNull

end FiniteFourier
end LinearAlgebra
end OAI
