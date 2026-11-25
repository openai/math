import OAI.Hierarchy.ProbeCoreBoard

namespace OAI
/-! # Address width of the fixed global site numbering -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe
open scoped Classical

/-- The fixed row-order numbering of the actual physical board. The two
exterior families alone already contain an origin, even at zero height. -/
def siteLast (h d k : ℕ) := Fintype.card (Site h d k)-1

def siteNumber (h d k : ℕ) : Site h d k ≃ Fin (siteLast h d k+1) :=
  (Fintype.equivFin _).trans (finCongr (by
    have nonempty : Nonempty (Site h d k) := ⟨(.inl 0,none)⟩
    have pos := Fintype.card_pos_iff.mpr nonempty
    unfold siteLast
    omega))

def siteFactor (d k : ℕ) :=
  (2+2*(18*(d-1)+1)*4^(rounds d+1))*(1+2*k)

theorem site_count (h d k : ℕ) (positive : 1≤d) :
    siteLast h d k+1 ≤ siteFactor d k*2^h := by
  let π := Equiv.refl (Fin (2^h))
  have shape := (advisedRoute h d π).layer_shapes
  have count : (permutationFabric h d).shapes.length=18*(d-1)+1 :=
    (show (advisedRoute h d π).layers.length=(permutationFabric h d).shapes.length by
      simpa only [List.length_map] using congrArg List.length shape).symm.trans (advised_length ..)
  have cols : Fintype.card (Columns h d) ≤
      2*2^h+2*(18*(d-1)+1)*(4^(rounds d+1)*2^h) := calc
    _ ≤ 2*2^h+2*(permutationFabric h d).shapes.length*(4^(rounds d+1)*2^h) :=
      payloadColumns_card_le h d positive
    _ = _ := by rw [count]
  have labels := Fintype.card_congr (siteNumber h d k)
  simp only [Site,Columns,ColumnSite,Fintype.card_prod,Fintype.card_fin,ColumnLayer,
    Fintype.card_option,Fintype.card_bool] at labels
  rw [←labels]
  calc
    _ ≤ _ := Nat.mul_le_mul_right _ cols
    _ = _ := by dsimp only [siteFactor]; ring

/-- The actual site identifiers fit in h plus a public constant number of bits. -/
def siteExtra (d k : ℕ) := Nat.log 2 (siteFactor d k)+1

theorem site_address (h d k : ℕ) (positive : 1≤d) :
    siteLast h d k+1 ≤ 2^(h+siteExtra d k) := by
  have cap : siteFactor d k ≤ 2^siteExtra d k :=
    (Nat.lt_pow_succ_log_self (by decide) (siteFactor d k)).le
  rw [pow_add,mul_comm]
  exact (site_count h d k positive).trans (Nat.mul_le_mul_right _ cap)

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
