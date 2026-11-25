import OAI.Hierarchy.DescentResetStencilPitch

namespace OAI
/-! The signed output field and the complete gather key both fit the shared stencil pitch. -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentPlainTerminal.Suffix DescentGLPacked
noncomputable section

theorem stencil_lane_room (S : StencilBook) (e h w : ℕ) (positive : 0 < S.b)
    (wide : 4*sharedWidth S ≤ h) (chosen : e ≤ Stencil.laneExponent S.c (sharedWidth S) h)
    (word : h ≤ w) :
    2^e*max (S.n*Stencil.count S.r (S.degree+S.degree)) (S.t*2^S.r) ≤ w/2 ∧ S.n*2^e ≤ w :=by
  let u:=sharedWidth S
  have selected : (u+u)*2^e ≤ h/2 :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (n:=2) (by decide) chosen)).trans
      (lane_fit S.c u h (positive_width S positive) wide)
  have part : Stencil.stencilUnit S.r S.m S.degree S.n S.t ≤ u:=
    (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  obtain ⟨gather,rest⟩:=max_le_iff.mp part
  have sink:=(max_le_iff.mp (max_le_iff.mp rest).2).1
  have a : S.n*Stencil.count S.r (S.degree+S.degree) ≤ u:=(Nat.le_add_right ..).trans gather
  have b : S.t*2^S.r ≤ u:=(Nat.mul_le_mul_right _ (Nat.le_add_right S.t S.n)).trans sink
  have field : S.n ≤ u:=(Nat.le_add_left ..).trans gather
  have bound {x : ℕ} (hx : x ≤ u) : x*2^e ≤ h/2:=
    (Nat.mul_le_mul_right _ (hx.trans (Nat.le_add_right u u))).trans selected
  constructor
  · rw [Nat.mul_comm]
    exact (bound (max_le a b)).trans (Nat.div_le_div_right word)
  · exact (bound field).trans ((Nat.div_le_self ..).trans word)

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
