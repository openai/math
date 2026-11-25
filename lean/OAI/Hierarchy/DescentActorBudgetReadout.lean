import OAI.Hierarchy.DescentTerminalBudget
import OAI.Hierarchy.DescentResetAtomLedger

namespace OAI
/-! # From the paid endpoint quantities to actual weights of each installed local tensor -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentMixedRouter DescentChosenRouter DescentResetAttachments DescentNetworkSubstitution
open scoped Classical BigOperators
noncomputable section
variable {F P H : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht)
variable (T : Terminals Z) (old : A.graph.Site→List H) (wire hist f g B : ℕ)
local notation "R" => Z.placement
local notation "M" => 2^g*B
local notation "S₀" => 2^f*B
local notation "whole" => bin T.home (A.siteUnits Z.hub old wire 256 hist)
local notation "weight" => terminalWeight Z.unit Z.placement.contact Z.placement.owner
variable (bill : ActorBudget Z T old wire hist f g B)

theorem end_cap (s : Bool) (t : Z.Fallback) :
    bin (T.home ∘ ends A.graph s) A.graph.width t*wire*(if T.hub t then 256 else 1)≤whole t := by
  rw [←show T.hub ∘ T.home=Z.hub from funext T.tag,whole_fiber]
  cases s
  · dsimp only [ends]
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right wire (Nat.le_add_right _ _))).trans
      (Nat.le_add_right _ _)
  · dsimp only [ends]
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right wire (Nat.le_add_left _ _))).trans
      (Nat.le_add_right _ _)

theorem fall_traffic (s : Bool) (t : Z.Fallback) :
    weight s (.inr t)*wire*(if T.hub t then 256 else 1)≤whole t := by
  have routed := fallback_bin (R) Z.unit s t
  have key : (fun e=>(R).fall s ((R).old s e))=T.home ∘ ends A.graph s := funext fun e=>(T.attach s e).symm
  have widths : (fun _ : A.graph.Edge => Z.unit) = A.graph.width :=
    funext fun e => (Z.allWidths e).symm
  rw [key,widths] at routed
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right wire routed)).trans (end_cap Z T old wire hist s t)

include bill in
private theorem ordinary_bound (t : Z.Fallback) (atT : T.hub t=false) : (whole t:ℝ)≤3*(S₀:ℝ) := by
  have bound := bill.ordinary t atT
  have y : (1:ℝ)≤(2^Z.n:ℕ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.two_pow_pos _)
  have numerator : 0 ≤ (3:ℝ)*((2^f*B:ℕ):ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have upper := bound.trans (div_le_self numerator y)
  push_cast at upper ⊢
  exact upper

private theorem scaled_three {v load : ℕ} (wire : ℕ) (node : v ≤ 3*load) :
    (wire:ℝ)*(v:ℝ) ≤ (wire:ℝ)*(3*(load:ℝ)) := by
  exact_mod_cast Nat.mul_le_mul_left wire node

include bill in
theorem port_price (p : Z.bank.Site) {limit : ℝ}
    (baseScale : 3*(2+rotorRate h C)*(S₀:ℝ)≤limit)
    (ordinaryScale : 9*(S₀:ℝ)≤limit)
    (hubScale : 3*(M:ℝ)/256≤limit) :
    (wire:ℝ)*portLoad Z.bank p≤limit := by
  rcases p with ⟨⟨s,z⟩,p⟩
  have read := bank_portLoad Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align
    (selected (R) Z.graph Z.positive Z.pay Z.circuit) ⟨(s,z),p⟩
  rw [show portLoad Z.bank ⟨(s,z),p⟩=_ from read]
  cases z with
  | inl good =>
    let c := selected (R) Z.graph Z.positive Z.pay Z.circuit s (.inl good)
    have node := ordinary_actor Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align s
      (.inl good) c rfl p
    have scaled := mul_le_mul_of_nonneg_left node (Nat.cast_nonneg wire : (0:ℝ)≤wire)
    have amount := bill.good s good
    have reserve := mul_le_mul_of_nonneg_left bill.reserve (show 0≤rotorRate h C by unfold rotorRate;positivity)
    apply scaled.trans
    change (wire:ℝ)*(3*((weight s (.inl good):ℝ)+rotorRate h C*Z.pay))≤limit
    push_cast at amount reserve baseScale ⊢
    linarith only [amount,reserve,baseScale]
  | inr t =>
    let c := selected (R) Z.graph Z.positive Z.pay Z.circuit s (.inr t)
    have node := exceptional_actor Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align s
      (.inr t) c rfl p
    apply (scaled_three wire node).trans
    have contact := fall_traffic Z T old wire hist s t
    cases hv : T.hub t
    · simp only [hv,ite_false,Bool.false_eq_true,mul_one] at contact
      have cost : (weight s (.inr t):ℝ)*wire≤(whole t:ℝ) := by exact_mod_cast contact
      have small := ordinary_bound Z T old wire hist f g B bill t hv
      linarith only [ordinaryScale,small,cost]
    · simp only [hv,ite_true] at contact
      rw [bill.hub t hv] at contact
      have cost : (weight s (.inr t):ℝ)*wire*256≤(M:ℝ) := by exact_mod_cast contact
      linarith only [cost,hubScale]

include bill in
theorem cumulative_port_cap (p : Z.bank.Site)
    (baseScale : 3*(2+rotorRate h C)*(S₀:ℝ)+hist≤M)
    (ordinaryScale : 9*(S₀:ℝ)+hist≤M)
    (hubScale : 3*(M:ℝ)/256+hist≤M) :
    wire*portLoad Z.bank p+hist≤M := by
  have estimate := port_price Z T old wire hist f g B bill p (limit:=(M:ℝ)-hist)
    (by linarith only [baseScale]) (by linarith only [ordinaryScale]) (by linarith only [hubScale])
  exact_mod_cast (show (wire:ℝ)*portLoad Z.bank p+hist≤(M:ℝ) by linarith only [estimate])

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
