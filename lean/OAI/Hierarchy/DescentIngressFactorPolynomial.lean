import OAI.Hierarchy.DescentHaloWalkRAM
import Mathlib.Tactic

namespace OAI
/-! # Public scalar polynomial in the old degree, block count and capacity -/
namespace Hierarchy.DescentOrdinaryVenueIngress

def ingressFactor (D r c : ℕ) : ℕ :=
  let P:=(D+1)^4
  let L:=6*P+1
  let T:=P+1+(1+P)
  let walk:=40*(D+10)^4+4
  let sort:=200*(P+1)^3+4
  let halo:=(16+10*(L+T)+P*(walk+sort))+
    7*(15*(L+1)+15*(T+1)+(11+4*(20*(D+10)^4))+(11+4*(100*(P+1)^3)))
  2*(2048*6)+640*4+8192*(r*(1+c*6)+1)+halo+
    8192*(P+1)^2*((P*r)*(1+c*6)+1)

theorem ingressFactor_le (D r c U : ℕ) (large : 16384 ≤ U)
    (degree : D ≤ U) (blocks : r ≤ U) (capacity : c ≤ U) : ingressFactor D r c ≤ U^20 := by
  calc
    _ ≤ ingressFactor U U U := by dsimp only [ingressFactor]; gcongr
    _ ≤ U^20 := by
      obtain ⟨x,rfl⟩:=Nat.exists_eq_add_of_le large
      dsimp only [ingressFactor]
      zify
      apply sub_nonneg.mp
      ring_nf
      positivity

end Hierarchy.DescentOrdinaryVenueIngress

end OAI
