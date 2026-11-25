import OAI.Optimization.LinearProgramming.Farkas.Subspace

/-! The homogeneous slack columns and uniqueness of the oriented point on a line. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

open Matrix
open scoped Matrix

variable {K : Type*} [Field K] {m d n : ℕ}

/-- Explicit column presentation of `(β,u) ↦ (β,βb−Au)`. -/
def slackColumns (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    Matrix (Fin (m+1)) (Fin (d+1)) K :=
  Fin.cons (Fin.cons 1 (fun _ => 0)) (fun i => Fin.cons (b i) (fun j => -A i j))

theorem slackColumns_mulVec (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (z : Fin (d+1) → K) :
    slackColumns A b *ᵥ z = Farkas.slackMap A b (z 0, Fin.tail z) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (Fin.cons 1 (fun _ : Fin d => (0 : K)) ⬝ᵥ z) = z 0
    simp [dotProduct, Fin.sum_univ_succ]
  · change (Fin.cons (b j) (fun a => -A j a) ⬝ᵥ z) = z 0 * b j - A j ⬝ᵥ Fin.tail z
    simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, neg_mul,
      Finset.sum_neg_distrib, Fin.tail]
    ring

theorem slackColumns_range (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    LinearMap.range (slackColumns A b).mulVecLin = LinearMap.range (Farkas.slackMap A b) := by
  ext w
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨(z 0,Fin.tail z),(slackColumns_mulVec A b z).symm⟩
  · rintro ⟨⟨β,u⟩,rfl⟩
    refine ⟨Fin.cons β u,?_⟩
    change slackColumns A b *ᵥ Fin.cons β u = _
    simp [slackColumns_mulVec]

/-- A one-dimensional subspace contains at most one point with marked entry one. -/
theorem marked_line_unique (W : Submodule K (Fin n → K)) (i : Fin n) (h : Module.finrank K W = 1)
    {x y : Fin n → K} (hx : x ∈ W) (hy : y ∈ W) (hxi : x i = 1) (hyi : y i = 1) : x = y := by
  have hx₀ : x ≠ 0 := fun e => one_ne_zero (α := K) (by rw [← hxi,e]; rfl)
  have line := eq_span_singleton_of_mem_of_finrank_eq_one h hx hx₀
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (line ▸ hy)
  have hi : a * x i = y i := congrFun ha i
  have ha₁ : a = 1 := by simpa [hxi,hyi] using hi
  simpa [ha₁] using ha

end Recovery
end LinearProgramming
end Optimization
end OAI
