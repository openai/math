import OAI.Computability.BorderVNP.PackedFrozenBirthSection
import OAI.Computability.BorderVNP.PackedFrozenLayerCost
import OAI.Computability.BorderVNP.PackedInheritedHookQuery
import OAI.Computability.BorderVNP.PackedInheritedHookCode
import OAI.Computability.BorderVNP.PackedFrozenRowCapacity
import OAI.Computability.BorderVNP.PackedDeckScoreCost

/-! # Gate bound of all fresh frozen sections of one physical combining node -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Node

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals CellAddressCircuit
open InheritedProfile BankJoint VPVNP.VerifierNetwork PackedDeckScore
open private view_cubic from OAI.Computability.BorderVNP.PackedFrozenLayerCost
open private padded from OAI.Computability.BorderVNP.PackedRoutingCost
open scoped Classical

variable {D m s old np n C C' d d' k k' w W : ℕ} [NeZero D] {K : Type*} [Field K]
  (e : PaidIdentity K D m) (first : Fin D × Bool) (hm : 0 < m)
  {A : Type} [Fintype A] (seed : A ↪ Fin n)
  {σ R B : Type*} [Fintype σ] [Fintype R] [Fintype B] (carried : Frame σ (Pins R B d'))
  (F : Fields s old np C d k w σ) (newF : Fields (siteCapacity e s n) (edgeCapacity e old n) np C' d' k' w σ)
  (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w)) (counts : Frame σ (A × Option (Fin e.count) × Fin w))
  (work extent : Fin s → Fin w → σ) (occupied : Fin old → σ) (ports : Fin np → Bool)
  (successor : Fin (edgeCapacity e old n) → σ)

local notation3 "V" => siteCapacity e s n
local notation3 "E" => edgeCapacity e old n
local notation3 "hooks" => InheritedHook.Row old D
local notation3 "targets" => A × (Fin D × Bool)
local notation3 "ops" => adjustNodes e + BankCircuit.headerNodes D e.count m + PaidBox.nodeBound e + nodes e first

omit [NeZero D] in
/-- The fixed coefficient of the fresh gate cost, independent of the
geometric arrays and the supplied histogram. -/
noncomputable def freshCoefficient := 400000+mainRows e first+100*(ops+InheritedHook.nodes e)

include seed in
/-- Both seed emitters, with every immutable owner bit, physical incidence scan and
terminal query. Their cost is linear in the true sewn row count times a cubic word cost. -/
theorem fresh_cubic (hp : np ≤ s)
    (widths : d' ≤ W ∧ w ≤ W ∧ Nat.clog 2 (12*(V+E+1)) ≤ W) :
    (Fintype.card (Birth.Row e first A)*(1+d') + (counts.size+(Views.frame newF).size+6+
      Fintype.card A*(ops*(100*(w+1)^2)))) +
      (counts.size+queryCost (batchBits targets hooks) d' w+
        cut.size+(Views.frame newF).size+1+Fintype.card hooks*(InheritedHook.nodes e*(100*(w+1)^2))) ≤
    2*counts.size+cut.size+freshCoefficient e first*(V+E+1)*(W+1)^3 := by
  let vol := V+E+1
  let unit := vol*(W+1)^3
  have uv : 0 < vol := Nat.succ_pos _
  have uu : 0 < unit := Nat.mul_pos uv (by positivity)
  have geom := LayerRows.volume (s := s) (old := old) (np := np) (seeds := n) e hp
  have view := view_cubic (R := 12*vol) (W := W) newF (by omega) ⟨widths.1,widths.2.1,widths.2.2⟩
  have nA : Fintype.card A ≤ n := by simpa using Fintype.card_le_of_injective seed seed.injective
  have nt : 1 ≤ Fintype.card (TemplateSite e) := Fintype.card_pos
  have ts : D*2 ≤ Fintype.card (TemplateSite e) := by simp only [TemplateSite,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]; omega
  have seeds : Fintype.card A ≤ vol := nA.trans ((Nat.le_mul_of_pos_right n nt).trans (by dsimp [vol,siteCapacity]; omega))
  have target : Fintype.card targets ≤ V := by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    exact (Nat.mul_le_mul nA ts).trans (Nat.le_add_left _ _)
  have hook : Fintype.card hooks ≤ E := by
    simp only [InheritedHook.Row,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,edgeCapacity_eq]
    nlinarith only [Nat.zero_le (D*old),Nat.zero_le old,Nat.zero_le (Fintype.card (TemplateEdge e)*n)]
  have qsum : Fintype.card targets + Fintype.card hooks ≤ vol := by dsimp [vol]; omega
  let b := batchBits targets hooks
  have hb : b ≤ W := (Nat.clog_mono_right 2 (qsum.trans (by omega : vol ≤ 12*vol))).trans widths.2.2
  have pow : 2^b ≤ 2*vol := padded qsum uv
  have range : b+d'+w+1 ≤ 3*(W+1) := by omega
  have query : queryCost b d' w ≤ 8100*unit := by
    apply (queryCost_le b d' w).trans
    exact (Nat.mul_le_mul pow (Nat.mul_le_mul_left 150 (Nat.pow_le_pow_left range 3))).trans_eq (by dsimp [unit]; ring)
  have cube : (w+1)^2 ≤ (W+1)^3 :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ widths.2.1) 2).trans (Nat.pow_le_pow_right (by positivity) (by decide : 2≤3))
  have codeword : 1+d' ≤ (W+1)^3 :=
    (show 1+d' ≤ W+1 by omega).trans (by exact Nat.le_self_pow (by decide) _)
  have cap (N c : ℕ) (hN : N ≤ vol) : N*(c*(100*(w+1)^2)) ≤ (100*c)*unit := by
    exact (Nat.mul_le_mul hN (Nat.mul_le_mul_left c (Nat.mul_le_mul_left 100 cube))).trans_eq (by dsimp [unit]; ring)
  have owner : Fintype.card (Birth.Row e first A)*(1+d') ≤ mainRows e first*unit := by
    rw [main_card]
    exact (Nat.mul_le_mul (Nat.mul_le_mul_right _ seeds) codeword).trans_eq (by dsimp [unit]; ring)
  have hookCost := cap _ (InheritedHook.nodes e) (hook.trans (by dsimp [vol]; omega))
  have mainCost := cap _ ops seeds
  have hview : (Views.frame newF).size ≤ 38400*unit := view.trans_eq (by dsimp [unit]; ring)
  have scaled : freshCoefficient e first*vol*(W+1)^3 =
      400000*unit+mainRows e first*unit+(100*ops)*unit+(100*InheritedHook.nodes e)*unit := by
    unfold freshCoefficient
    dsimp only [unit]
    ring
  change _ ≤ 2*counts.size+cut.size+freshCoefficient e first*vol*(W+1)^3
  rw [scaled]
  change queryCost (batchBits targets hooks) d' w ≤ 8100*unit at query
  omega

end Packing.Inherited.FrozenTape.Node

end BorderVNP
end Computability
end OAI
