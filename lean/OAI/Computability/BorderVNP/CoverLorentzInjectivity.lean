import OAI.Computability.BorderVNP.CoverLorentzPlane

/-!
# Uniform local injectivity of the congruence covers

The base group brings any center into one compact Dirichlet tile. Normality of
each deeper level preserves the subgroup under this conjugation. Properness of
the action bounds the conjugates moving points of the tile a fixed distance,
and the nested congruence groups eventually exclude all those except the identity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Set Matrix UpperHalfPlane
open scoped Pointwise MatrixGroups

/-- For any fixed displacement bound, all sufficiently deep levels exclude nonidentity
translations of that size uniformly over the centers in the hyperbolic plane. -/
theorem eventually_no_short_move (r : ℝ) :
    ∃ l, ∀ d ≥ l, ∀ (u : gamma d) (z : ℍ), dist (gammaSL d u • z) z ≤ r → u = 1 := by
  obtain ⟨R,_,hR⟩ := dirichlet_bounded 1
  let B := Metric.closedBall I (r+R)
  let S := {g : SL(2,ℝ) | (g • dirichlet 1 ∩ B).Nonempty}
  have hS : IsCompact S := ProperSMul.isCompact_setOfPred_inter_nonempty (dirichlet_compact 1)
    (ProperSpace.isCompact_closedBall I (r+R))
  obtain ⟨l,hl⟩ := eventually_identity_on_compact (hS.image continuous_subtype_val)
  refine ⟨l,?_⟩
  intro d hd u z hu
  obtain ⟨v,hv⟩ := exists_mem_dirichlet 1 z
  let w : gamma d := ⟨v.val * u.val * v.val⁻¹, (gammaNormal d).conj_mem _ u.2 _⟩
  have hw : gammaSL d w * gammaSL 1 v = gammaSL 1 v * gammaSL d u := by
    apply Subtype.ext
    change split (↑(v.val*u.val*v.val⁻¹) : Order) * split v.val.val = split v.val.val * split u.val.val
    rw [← map_mul,← map_mul]
    apply congrArg split
    change (((v.val*u.val)*v.val⁻¹)*v.val : Orderˣ).val = (v.val*u.val).val
    rw [mul_assoc (v.val*u.val),inv_mul_cancel,mul_one]
  have hm : gammaSL d w ∈ S := by
    let y := gammaSL 1 v • z
    refine ⟨gammaSL d w • y,⟨y,hv,rfl⟩,?_⟩
    change dist (gammaSL d w • y) I ≤ r+R
    have he : gammaSL d w • y = gammaSL 1 v • (gammaSL d u • z) := by
      change gammaSL d w • (gammaSL 1 v • z) = _
      rw [← mul_smul,hw,mul_smul]
    have he' : dist (gammaSL d w • y) y ≤ r := by
      rw [he]
      exact (dist_smul (gammaSL 1 v) (gammaSL d u • z) z) ▸ hu
    exact (dist_triangle _ y I).trans (add_le_add he' (hR hv))
  have he := hl d hd w ⟨gammaSL d w,hm,rfl⟩
  change v.val * u.val * v.val⁻¹ = 1 at he
  exact Subtype.ext (by simpa [mul_assoc] using congrArg (fun a : Orderˣ => v.val⁻¹*a*v.val) he)

/-- In sufficiently deep quotients no translated copy of an endpoint shortens a distance
inside a ball of a prescribed radius. This is the distance-preservation part of lifting balls. -/
theorem eventually_ball_distances (r : ℝ) :
    ∃ l, ∀ d ≥ l, ∀ (o x y : ℍ), x ∈ Metric.closedBall o r → y ∈ Metric.closedBall o r →
      ∀ u : gamma d, dist x y ≤ dist x (gammaSL d u • y) := by
  obtain ⟨l,hl⟩ := eventually_no_short_move (4*r)
  refine ⟨l,?_⟩
  intro d hd o x y hx hy u
  by_contra! h
  have he : dist x y ≤ r+r := (dist_triangle x o y).trans
    (add_le_add hx (by simpa [dist_comm] using hy))
  have hm : dist (gammaSL d u • y) y ≤ 4*r := by
    have hh := dist_triangle (gammaSL d u • y) x y
    rw [dist_comm (gammaSL d u • y) x] at hh
    linarith
  have h1 := hl d hd u y hm
  simp [h1] at h

end Cover

end BorderVNP
end Computability
end OAI
