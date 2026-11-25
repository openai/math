import OAI.Hierarchy.ProbeConfiguredFormat
import OAI.Hierarchy.ProbeCommodityBounds
import OAI.Hierarchy.ProtocolRAMCalendarNativeAccounts
import OAI.Hierarchy.ProtocolRAMCalendarRouteBox
import OAI.Hierarchy.ProtocolRAMCalendarBudget

namespace OAI
/-! # Settlement of the originally chosen protocol at its actual terminal memory -/

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

def account {z arity goods : ℕ} (arena : Arena) (f : Attempt→Format z (2^v.W) k arity goods)
    (initial width : ℕ) (bills : Event→WordRows) :=
  let N := CoreBoard.Stages z (2^v.W)
  nativeAccounts (N:=N) v.mesh arena f initial width bills
    (coreDebit v.sampler z (2^v.W) k p q Q Λ (dyadicScale v.W) v.radius)
    v.a v.radius (probeBonus v.W) (routeCap N v.radius)

private theorem fixed_positive : 0<(v.W:ℝ) ∧ 0<probeBonus v.W ∧ 0<probeMotion k v.W ∧
    0<probeDensity k v.W ∧ 0<purchaseReward k v.W ∧ 0<v.loss := by
  have w : 0<(v.W:ℝ) := by exact_mod_cast (show 0<v.W from (by have:=v.geometry.wide;omega))
  have t : 0<dyadicScale v.W := by unfold dyadicScale; positivity
  have s : 0<probeHeat v.W := pow_pos t _
  have n : 0<(publicStages v.W:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have h : 0<(publicTiles k v.W:ℝ) := Nat.cast_pos.mpr v.geometry.tiles
  have kh : 0<(k:ℝ) := Nat.cast_pos.mpr v.positive
  have b : 0<probeBonus v.W := by unfold probeBonus; positivity
  have u : 0<probeMotion k v.W := by unfold probeMotion; positivity
  have d : 0<probeDensity k v.W := by unfold probeDensity; positivity
  have r : 0<purchaseReward k v.W := by unfold purchaseReward; positivity
  have box : 0≤upperBox (publicStages v.W) v.radius := (Nat.cast_nonneg _).trans (le_max_left ..)
  exact ⟨w,b,u,d,r,div_pos v.geometry.cutoff.1 (by unfold wallCap; positivity)⟩

theorem fixed_initial {z w arity goods : ℕ} (arena : Arena) (f : Attempt→Format z (2^v.W) k arity goods)
    (initial width : ℕ) (bills : Event→WordRows) (mem : Memory w)
    (empty : ∀i : Commodity (Fin (2^z)) (CoreBoard.Stages z (2^v.W)) k,mem (initial+PurchaseInventory.slot i)=0) :
    let A := v.account arena f initial width bills
    A.bank.balance width 1 (A.read (.outer 0 0) mem)≤(2^z:ℕ) := by
  intro A
  let N:=CoreBoard.Stages z (2^v.W)
  have snapshot := nativeAccounts_initial (N:=N) v.mesh arena f initial width bills
    (coreDebit v.sampler z (2^v.W) k p q Q Λ (dyadicScale v.W) v.radius)
    v.a v.radius (probeBonus v.W) (routeCap N v.radius) mem
  change (A.read (.outer 0 0) mem).bits=(fun i=>(mem (initial+PurchaseInventory.slot i)).val) ∧
    (A.read (.outer 0 0) mem).paid=coreDebit v.sampler z (2^v.W) k p q Q Λ (dyadicScale v.W) v.radius at snapshot
  apply A.bank.initial_balance
  · intro i
    change (A.read (.outer 0 0) mem).bits i=0
    simpa only [empty,Fin.val_zero] using congrFun snapshot.1 i
  · change (0:ℝ)≤(v.a:ℝ)
    exact_mod_cast v.quadratic_pos.le
  · intro i
    change 0≤bonus (probeBonus v.W) i
    cases i <;> simp [bonus,v.fixed_positive.2.1.le]
  · change (A.read (.outer 0 0) mem).paid≤_
    rw [snapshot.2]
    unfold coreDebit
    rw [CoreBoard.invoice _ _ _ _ _ _ _ _ _ _ (by unfold dyadicScale; positivity)]
    have rate := v.geometry.core_capacity
    rw [←fixed_stage_count z v.W] at rate
    simpa only [mul_one] using mul_le_mul_of_nonneg_left rate (Nat.cast_nonneg (α:=ℝ) (2^z))

/-- Only the original installed finite readbacks and initial zero stock bank are
needed at this point. All numerical budgets, including both curvatures, fuel,
price ceiling and the initial core opening, come from the selected format. -/
theorem terminal {z w choices dim arity goods : ℕ} (arena : Arena)
    (f : Attempt→Format z (2^v.W) k arity goods) (initial width : ℕ) (bills : Event→WordRows)
    (C : Chart w choices dim) (clock : C.mesh=v.mesh) (mem : Memory w)
    (empty : ∀i : Commodity (Fin (2^z)) (CoreBoard.Stages z (2^v.W)) k,mem (initial+PurchaseInventory.slot i)=0)
    (wide : v.widthFloor≤width) :
    let A := v.account arena f initial width bills
    CalendarReadbacks A C mem (2^z) v.mesh.inject v.actualK v.limit v.finish ((dyadicScale v.W)^8) ((v.W:ℝ)⁻¹^2)
      v.loss v.menu.margin (probeDensity k v.W) (purchaseReward k v.W) →
    let final := A.read (.outer (C.mesh.inject+C.mesh.cool) 0) (run C (events C.mesh) mem)
    A.bank.cash final+pairing (A.bank.units width final) A.box≤6*(2^z:ℕ) := by
  intro A R final
  let N := CoreBoard.Stages z (2^v.W)
  let U := upperBox (publicStages v.W) v.radius
  let L : ℝ := (1+2*N*k:ℕ)
  have fixed : N=publicStages v.W := fixed_stage_count z v.W
  have vPos := v.fixed_positive
  have ha : 0<A.a := by
    change 0<(v.a:ℝ)
    exact_mod_cast v.quadratic_pos
  have hU : 0≤U := (Nat.cast_nonneg _).trans (le_max_left ..)
  have hs : 0<(v.finish:ℝ) := by exact_mod_cast v.clock.finish_pos
  have hs₁ : (v.finish:ℝ)≤1 := by exact_mod_cast v.clock.finish_le
  have base : 0<v.actualK := Nat.mul_pos v.clock.base_pos (by unfold commonWidth;omega)
  have row (i) : A.box i∈Set.Icc 0 U := by
    change routeCap N v.radius (PurchaseInventory.lane i)∈Set.Icc 0 U
    simpa only [U,upperBox,←fixed,N] using routeCap_range (k:=k) (h:=z) (d:=2^v.W) v.radius (Nat.cast_nonneg _) i
  have flow := commodity_outer_bounds A.bank width v.mesh.inject v.finish U (probeBonus v.W) v.clock.inject_pos hs hs₁ ha
    (Nat.cast_nonneg _) hU vPos.2.1.le row rfl rfl
  have coeff (i : Commodity (Fin (2^z)) N k) : A.coefficient i≤probeBonus v.W := by
    change bonus (probeBonus v.W) i≤probeBonus v.W
    cases i with
    | inl _ => exact vPos.2.1.le
    | inr _ => exact le_rfl
  have norm : (v.finish:ℝ)*(((v.a:ℝ)+probeBonus v.W)*U^2*(1+2*N*k:ℕ))≤1 := by
    rw [fixed]
    exact v.clock.normalized.le
  have stop := commodity_terminal_score (v.a:ℝ) v.radius (probeBonus v.W) U v.finish A.coefficient A.box
    ha.le (Nat.cast_nonneg _) vPos.2.1.le hU hs.le coeff row norm
  have time := dyadic_cooling_integral v.W ((le_max_left ..).trans v.geometry.wide)
  have size_eq : L=((1+2*publicStages v.W*k:ℕ):ℝ) := by
    change ((1+2*N*k:ℕ):ℝ)=_
    rw [fixed]
  have size_nonneg : 0≤L := Nat.cast_nonneg _
  have energy_nonneg : 0≤((v.a:ℝ)+probeBonus v.W)*U^2*L :=
    mul_nonneg (mul_nonneg (add_nonneg (by exact_mod_cast v.quadratic_pos.le) vPos.2.1.le)
      (sq_nonneg U)) size_nonneg
  have exhausted := v.clock.exhausted
  have gradients := v.clock.gradient
  rw [v.clock.same_mesh] at gradients
  apply R.terminal (by positivity) v.clock.inject_pos (v.clock.inject_width.trans wide) base vPos.2.2.2.2.2 v.menu.margin_pos
    vPos.2.2.2.1 vPos.2.2.2.2.1 hs hs₁ time.1 time.2.1 (by positivity) v.geometry.cooling
    (V:=1) (G:=(v.limit:ℝ)^2*L) (P:=U) (Q:=((v.a:ℝ)+probeBonus v.W)*U^2*L)
    (by norm_num) (mul_nonneg (sq_nonneg _) size_nonneg) hU energy_nonneg v.clock.variation
    _ _ (v.fixed_initial arena f initial width bills mem empty) _ _
  · change (v.limit:ℝ)^2*L≤(v.finish:ℝ)*(v.a:ℝ)*v.mesh.inject
    rw [size_eq]
    exact gradients
  · change OuterBounds A.bank (Fintype.card (Fin (2^z))) width v.mesh.inject v.limit
      (v.finish:ℝ) 1 ((v.limit:ℝ)^2*L) U (((v.a:ℝ)+probeBonus v.W)*U^2*L) at flow
    rw [Fintype.card_fin] at flow
    exact flow
  · change (v.finish:ℝ)*score (v.a:ℝ) (v.radius:ℝ) A.coefficient A.box≤((2^z:ℕ):ℝ)
    simpa only [Fintype.card_fin] using stop
  · rw [clock,size_eq]
    exact exhausted


end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI
