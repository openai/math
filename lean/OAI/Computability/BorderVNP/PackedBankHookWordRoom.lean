import OAI.Computability.BorderVNP.PackedBankSelectedWordRoom
import OAI.Computability.BorderVNP.PackedBankLocalPopulation
import OAI.Computability.BorderVNP.PackedFrozenHookSection
import OAI.Computability.BorderVNP.PackedHistorySeedWord
import OAI.Computability.BorderVNP.PackedInheritedWorkHorizon

/-! # Hook address room at every selected inner node

At each node the measured population constant depends on its prepared bins.
The sum of the finitely many node coefficients is fixed before the input and
processor counts. The expanded bank bound at the selected horizon controls
both the scaled hook addresses and the doubled successor extent.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Shortening Packing Packing.Inherited Packing.InheritedBank Packing.CoverScale
open Diagonal TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The explicit physical hook address bound at every selected shortening node. -/
def Compiled.HookRoom (S : SiteSchedule e) (T w B : ℕ) : Prop :=
  ∀ t < T, ∀ i : Fin S.rounds,
    let b := widthBudget S (S.publicProgramFactor^t*B) i.val
    HookTape.sourceRoom e (0,false) (loadMultiplier e*(S.source.pattern i).record*S.fanIn*b)
      ((measured_population_cap (I := Cube D) (B := (S.source.pattern i).bins.Bin) e S.saving).choose*
        ((S.source.pattern i).record*S.fanIn*b)) < 2^w

private theorem sourceRoom_scaled_le (a b T : ℕ) :
    HookTape.sourceRoom e (0,false) (a*T) (b*T) ≤ HookTape.sourceRoom e (0,false) a b*(T+1) := by
  let extra := BankJoint.addressCoefficient e (0,false)*(BankCharges.bound e*a+a+T)+b
  exact (Nat.le_add_right (HookTape.sourceRoom e (0,false) (a*T) (b*T)) extra).trans_eq
    (by dsimp only [extra, HookTape.sourceRoom]; ring)

private theorem fixed_factor_word_fit {n r A M : ℕ} (hr : 1 ≤ r) (ha : A ≤ n) (hm : M ≤ n) :
    A*(M+1) < 2^(60*logWidth r n) := by
  have fits := Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r hr)
  calc
    A*(M+1) < 2^logWidth r n*(M+1) := Nat.mul_lt_mul_of_pos_right (ha.trans_lt fits) (Nat.succ_pos _)
    _ ≤ 2^logWidth r n*2^logWidth r n := Nat.mul_le_mul_left _ (hm.trans_lt fits)
    _ = 2^(logWidth r n+logWidth r n) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The native hook source and twice the successor budget fit the selected word at
every stage of every active epoch, using the original seed multiplicity and epoch count. -/
theorem eventually_calibrated_hook_word_room {a x : ℕ} (s : EpochScales S a x) (dim : 1 ≤ a)
    (headerFactor : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n:ℝ)^ω) →
      ∀ d, d+1 = initialDepth (Fin (Fintype.card (Cube D))) r n →
      ∀ t < epochs (s.τ : ℝ) n, ∀ i : Fin S.rounds,
      let B := initialMass (D := D) n r d (width n (s.α : ℝ)) headerFactor
      let bound := widthBudget S (S.publicProgramFactor^t*B)
      let step := (S.source.pattern i).record*S.fanIn
      HookTape.sourceRoom e (0,false) (loadMultiplier e*(S.source.pattern i).record*S.fanIn*bound i.val)
          ((measured_population_cap (I := Cube D) (B := (S.source.pattern i).bins.Bin) e S.saving).choose*
            (step*bound i.val)) < 2^(60*logWidth r n) ∧
        2*bound (i.val+1) < 2^(60*logWidth r n) := by
  let V (i : Fin S.rounds) := (measured_population_cap (I := Cube D) (B := (S.source.pattern i).bins.Bin)
    e S.saving).choose
  let step (i : Fin S.rounds) := (S.source.pattern i).record*S.fanIn
  let bank (i : Fin S.rounds) := loadMultiplier e*(S.source.pattern i).record*S.fanIn
  let coefficient (i : Fin S.rounds) := HookTape.sourceRoom e (0,false) (bank i) (V i*step i)
  obtain ⟨ω, hω, caps⟩ := eventually_calibrated_bank_word_room S s dim headerFactor
  refine ⟨ω, hω, ?_⟩
  filter_upwards [caps, eventually_ge_atTop (∑ i, coefficient i), eventually_ge_atTop 1] with n room hcoeff hn
  intro r hr maxR d hd t ht i B bound
  let T := epochs (s.τ : ℝ) n
  let M := S.publicProgramFactor^T*B
  have cap : 7*M ≤ width n (1/5) ∧ 7*M < 2^(60*logWidth r n) := (room r hr maxR d hd).2
  have child : bound i.val ≤ M := widthBudget_horizon S B ht i.isLt.le
  have next : bound (i.val+1) ≤ M := widthBudget_horizon S B ht i.isLt
  have rounded : width n (1/5) ≤ n := Nat.floor_le_of_le (by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n) (by norm_num : (1/5:ℝ) ≤ 1))
  have total : M ≤ n := (Nat.le_mul_of_pos_left _ (by decide : 0 < 7)).trans (cap.1.trans rounded)
  have coeff := (Finset.single_le_sum (f := coefficient) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hcoeff
  constructor
  · change HookTape.sourceRoom e (0,false) (bank i*bound i.val) (V i*(step i*bound i.val)) < _
    rw [← Nat.mul_assoc (V i)]
    exact (sourceRoom_scaled_le (e := e) (bank i) (V i*step i) (bound i.val)).trans_lt
      (fixed_factor_word_fit hr coeff (child.trans total))
  · exact (Nat.mul_le_mul (by decide : 2 ≤ 7) next).trans_lt cap.2

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
