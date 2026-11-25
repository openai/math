import OAI.Hierarchy.ProtocolRAMCalendarAccounts

namespace OAI
/-! # Accounting for every actual attempt prior to the scheduled outer boundary -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe AdaptiveProbe.OuterBank
noncomputable section
variable {w q d : ℕ} {I : Type*} [Fintype I] {A : AccountColumns I} {C : Chart w q d}
  {mem : Memory w} {n m K cap : ℕ} {s₀ r scale ρ γ ρBuy reward : ℝ}
  (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward)

include R

/-- All trials following the first accepted low test are padded. Their
complete reserve subcalendars preserve the actual retained stock. -/
theorem CalendarReadbacks.stock_at_exit {j h : ℕ} (hj : j < m+m) (hh : h<C.mesh.outerFuel)
    (hit : observedMode C mem j h=1) :
    (A.trial C mem j C.mesh.outerFuel).bits=(A.trial C mem j h).bits := by
  have same (b : ℕ) (afterH : h≤b) (inside : b≤C.mesh.outerFuel) :
      (A.trial C mem j b).bits=(A.trial C mem j h).bits := by
    induction b, afterH using Nat.le_induction with
    | base => rfl
    | succ b hb ih =>
      have room : b<C.mesh.outerFuel := by omega
      have idle : observedMode C mem j b=0 ∨ observedMode C mem j b=1 := by
        rcases eq_or_lt_of_le hb with rfl | earlier
        · exact Or.inr hit
        · exact Or.inl (disabled_after_advance C mem j h b (R.law j hj) room earlier hit)
      exact (R.idle j hj b room idle).1.trans (ih room.le)
  exact same C.mesh.outerFuel hh.le le_rfl

/-- Every repair stage is measured between the two actual chronological stock
banks, after all reserve deliveries of the stage. -/
theorem CalendarReadbacks.trial_prices (hn : 0<n) (hm : 0 < m) (hw : m≤A.payloadWidth) (hK : 0<K)
    (hρ : 0<ρ) (hγ : 0<γ) (hρBuy : 0<ρBuy) (hrw : 0<reward) (hs : 0<s₀) (hs₁ : s₀≤1)
    {V G Cpay D : ℝ} (bound : OuterBounds A.bank n A.payloadWidth m cap s₀ V G Cpay D)
    {j : ℕ} (hj : j < m+m) :
    let price := fun h => A.bank.normalized A.payloadWidth n m s₀ j (A.trial C mem j h)
    price C.mesh.outerFuel ≤ price 0 ∧
      (ProbeCalendarLedger.exhaust (observedMode C mem) C.mesh.outerFuel j →
        price C.mesh.outerFuel ≤ price 0 - C.mesh.outerFuel * repairGain K ρ γ ρBuy reward) := by
  intro price
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have wp := hm.trans_le hw
  let s := phaseTime s₀ m j
  have times := clock_bounds hs hs₁ hm (j-m) (by omega)
  have sp : 0<s := hs.trans_le times.1
  have s1 : s≤1 := times.2
  apply ProbeCalendarLedger.attempt_telescope C.mesh.outerFuel (observedMode C mem j) price _
      (repairGain_pos hK hρ hγ hρBuy hrw).le (fun h _ => Nat.le_of_lt_succ (observedMode_lt C mem j h))
  · intro h hh idle
    obtain ⟨stock, cash⟩ := R.idle j hj h hh idle
    apply div_le_div_of_nonneg_right _ np.le
    change (A.trial C mem j (h+1)).paid + potential A.a A.M s A.coefficient A.box
      (fun i => ((A.trial C mem j (h+1)).bits i:ℝ)/A.payloadWidth) ≤
        (A.trial C mem j h).paid + potential A.a A.M s A.coefficient A.box
          (fun i => ((A.trial C mem j h).bits i:ℝ)/A.payloadWidth)
    rw [stock]
    exact add_le_add cash le_rfl
  · intro h hh active
    have saved : A.bank.balance A.payloadWidth s (A.trial C mem j (h+1)) ≤
        A.bank.balance A.payloadWidth s (A.trial C mem j h) - n*repairGain K ρ γ ρBuy reward := by
      rcases active with failed | bought
      · obtain ⟨record⟩ := R.failed j hj h hh failed
        have paid := FailedRows.decrease A.bank record wp hK hγ bound.aPos bound.bNonneg bound.MNonneg
          sp bound.boxNonneg (bound.capBound s sp s1)
        refine paid.trans (sub_le_sub_left ?_ _)
        exact (mul_le_mul_of_nonneg_left (min_le_left (ρ*γ/(8*K)) (ρBuy*reward/8)) np.le).trans_eq (by ring)
      · have receipt := A.purchase_readback C mem (R.bought j hj h hh bought)
        have paid := PurchaseReadback.decrease A.bank receipt wp hK hγ hρ hρBuy hrw hn
          bound.aPos bound.bNonneg bound.MNonneg sp s1 bound.boxNonneg bound.capBound
        refine paid.trans (sub_le_sub_left ?_ _)
        exact (mul_le_mul_of_nonneg_left (min_le_right (ρ*γ/(8*K)) (ρBuy*reward/8)) np.le).trans_eq (by ring)
    change A.bank.balance A.payloadWidth s (A.trial C mem j (h+1))/n ≤
      A.bank.balance A.payloadWidth s (A.trial C mem j h)/n - repairGain K ρ γ ρBuy reward
    apply (div_le_iff₀ np).2
    rw [sub_mul, div_mul_cancel₀ _ np.ne', mul_comm (repairGain K ρ γ ρBuy reward)]
    exact saved

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
