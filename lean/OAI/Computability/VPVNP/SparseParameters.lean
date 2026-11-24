import OAI.Computability.VPVNP.GrassmannSeeds
import Mathlib.Tactic.Linarith

/-!
# Parameters of the sparse Grassmann recursion

The strict Grassmann coefficient leaves room to enlarge it and pay the
triangle-inequality factor at each recursive step, while still growing
strictly more slowly than the plane dimension.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

/-- The index type of the uniform type-`r` pair law is inhabited. -/
theorem nonempty_pair {m r : ℕ} (hr : r ≤ m) : Nonempty (Pair m r) := by
  obtain ⟨a, b, hab⟩ := exists_pair hr
  exact ⟨⟨(a, b), hab⟩⟩

/-- Choice of the enlarged Grassmann coefficient and the triangle parameter
in Section 5.2. Their product lies strictly between one and the dimension. -/
theorem exists_sparse_parameters {m c₀ : ℝ} (hm : 1 < m) (hc₀ : c₀ < m) :
    ∃ c ε : ℝ, c₀ ≤ c ∧ 0 ≤ c ∧ 0 < ε ∧ 1 < c * (1 + ε) ∧ c * (1 + ε) < m := by
  let c := max 1 c₀
  have hc : 1 ≤ c := le_max_left _ _
  have hc' : c < m := max_lt hm hc₀
  have hp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  let ε := (m - c) / (2 * c)
  have hε : 0 < ε := div_pos (sub_pos.mpr hc') (mul_pos (by norm_num) hp)
  have hprod : c * (1 + ε) = (m + c) / 2 := by
    dsimp [ε]
    field_simp
    ring
  refine ⟨c, ε, le_max_right _ _, hp.le, hε, ?_, ?_⟩ <;> rw [hprod] <;> linarith

end Grassmann

end VPVNP
end Computability
end OAI
