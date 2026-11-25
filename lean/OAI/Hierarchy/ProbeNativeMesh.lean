import OAI.Hierarchy.ProbePhysicalCatalogue
import OAI.Hierarchy.ProbeReplayMeshBounds
import OAI.Hierarchy.ProbeRepairGain
import OAI.Hierarchy.ProbeRepairReplayAccount
import OAI.Hierarchy.ProbeOuterLedger
import OAI.Hierarchy.ProtocolRAMCalendarMesh

namespace OAI
/-! # Simultaneous fixed clock, catalogue copy scale and reserve fuel -/

namespace Hierarchy.ProtocolRAM.Calendar
open AdaptiveProbe AdaptiveProbe.OuterBank
open scoped BigOperators Classical
noncomputable section
universe u

/-- Numerical readout at the actual `Mesh`. The copied batch is normalized at the
single denominator `baseK * commonWidth` required by the native failed-row ledger. -/
structure ClockCalibration {J : Type*} [Fintype J] (menu : PacketWidths J) (N k : ℕ)
    (a β U cutoff repairDensity boughtDensity reward fee : ℝ) (s₀ : ℚ)
    (c : Mesh) (precision baseK minWidth : ℕ) : Prop where
  finish_pos : 0<s₀
  finish_le : s₀≤1
  same_mesh : c.cool=c.inject
  inject_pos : 0<c.inject
  inject_width : c.inject ≤ minWidth
  batch_width : 2*(baseK*commonWidth menu.width)*commonWidth menu.width ≤ minWidth
  reserve_pos : 0<c.reserveSteps
  reserve_width : c.reserveSteps ≤ minWidth
  inner_pos : 0<c.innerFuel
  outer_pos : 0<c.outerFuel
  normalized : (s₀:ℝ)*((a+β)*U^2*(1+2*N*k:ℕ))<1
  variation : 1≤a*c.inject
  gradient : (⌈2*(a+β)*U⌉₊:ℝ)^2*(1+2*N*k:ℕ)≤(s₀:ℝ)*a*c.cool
  base_pos : 0<baseK
  precision_pos : 0<precision
  lane_precision : 8*(1+2*N*k)≤precision
  precision_cutoff : 1/(precision:ℝ)+1/(precision:ℝ) ≤ cutoff
  local_rounding : ∀ j, 0 < menu.width j →
    (menu.ports : ℝ) * ((Finset.univ.sup menu.entries : ℕ) : ℝ) * (1/(precision:ℝ)) ≤
      (menu.width j : ℝ) * menu.margin / 2
  funds : ∀s≥(s₀:ℝ)/2,(menu.demands:ℝ)/baseK ≤ s*a*menu.margin
  rate : ∀s≥(s₀:ℝ)/2,∀ (I : Type u) [Fintype I] (rows edges n w : ℕ) (T : SelectedRows.Tape rows edges I),
    0<w → (Fintype.card I:ℝ)≤(1+2*N*k:ℕ)*n →
    (∀i,(Finset.univ.filter fun e=>T.activeKind e=some i).card≤1) →
    (∀e,∃j : J,baseK*(T.put (T.use e)+T.take (T.use e))≤w*menu.rate j) →
    (∑i,(stockChange T.kind (netUnits w T.put T.take) i)^2/(4*s*a))≤
      (n:ℝ)*repairDensity*menu.margin/(8*(baseK*commonWidth menu.width:ℕ))
  replay : ∀w≥minWidth,∀s≥(s₀:ℝ),∀n coords : ℕ,(coords:ℝ)≤(1+2*N*k:ℕ)*n →
    (c.reserveSteps:ℝ)*((coords:ℝ)*(2*U/w+(((⌈2*(a+β)*U⌉₊:ℝ)+2+⌈2*(a+β)*U⌉₊)/c.reserveSteps)^2/(2*s*a)))≤n*boughtDensity*reward/8
  saturated : fee+(1+2*N*k:ℕ)*⌈2*(a+β)*U⌉₊*U+boughtDensity*reward/8≤
    (c.innerFuel:ℝ)*(repairDensity*menu.margin/(8*(baseK*commonWidth menu.width:ℕ)))
  exhausted : 5-(c.outerFuel:ℝ)*repairGain (baseK*commonWidth menu.width) repairDensity menu.margin boughtDensity reward≤
    -(U+(a+β)*U^2*(1+2*N*k:ℕ)+1)

/-- Every replay tick uses at least half the smallest outer time. -/
theorem replay_above_floor {s s₀ : ℝ} (hs : 0 ≤ s₀) (later : s₀ ≤ s) (m j : ℕ) :
    s₀/2 ≤ replayTime s m j := by
  unfold replayTime
  have t : 0 ≤ s := hs.trans later
  have step : 0≤(j:ℝ)*(s/(2*m)) := by positivity
  linarith

/-- All prices, precision and limiting floor are chosen before the matching,
number of sites, payload width, or any private selector and its history. -/
theorem clock_calibration {J : Type*} [Fintype J] (menu : PacketWidths J) (N k : ℕ)
    (a β U cutoff ρ density reward fee : ℝ) (ha : 0<a) (hb : 0≤β) (hU : 0≤U)
    (hcut : 0<cutoff) (hρ : 0<ρ) (hden : 0<density) (hr : 0<reward) :
    ∃ (s₀ : ℚ) (c : Mesh) (Q K floor : ℕ),ClockCalibration.{u} menu N k a β U cutoff ρ density reward fee s₀ c Q K floor := by
  let dim := 1+2*N*k
  let cap := ⌈2*(a+β)*U⌉₊
  let score := (a+β)*U^2*dim
  obtain ⟨s₀,m,pos,last,small,steps,travel,square⟩ := rational_outer_mesh score 1 ((cap:ℝ)^2*dim) a ha
  have hot : 0<(s₀:ℝ) := by exact_mod_cast pos
  obtain ⟨Q,K,qpos,lanes,accurate,rounding,kpos,rates⟩ :=
    menu.native_rates.{u} dim (L:=(dim:ℝ)) ha (show 0<(s₀:ℝ)/2 by positivity) hρ hcut (by positivity)
  let denominator := K*commonWidth menu.width
  have denom : 0<denominator := Nat.mul_pos kpos (by unfold commonWidth; omega)
  obtain ⟨stepsI,minWidth,nonempty,umin,replay⟩ := reserve_mesh_bounds (dim:ℝ) U s₀ a density reward cap
    (Nat.cast_nonneg _) hU hot ha hden hr
  obtain ⟨inner,innerPos,innerPaid⟩ := reserve_repair_fuel fee dim U ρ menu.margin density reward denominator cap hρ menu.margin_pos denom
  have gain := repairGain_pos denom hρ menu.margin_pos hden hr
  obtain ⟨outer,paid⟩ := uniform_outer_fuel (C:=U) (D:=score) gain
  have outerPos : 0<outer := by
    by_contra h
    have dead : outer=0 := by omega
    rw [dead,Nat.cast_zero,zero_mul,sub_zero] at paid
    have scoreNonneg : 0 ≤ score := by dsimp [score]; positivity
    linarith
  let c : Mesh := ⟨m,m,outer,stepsI,inner⟩
  let cutoffWidth := max (max m minWidth) (2*denominator*commonWidth menu.width)
  have injectionFits : m ≤ cutoffWidth := (le_max_left m minWidth).trans (le_max_left ..)
  have reserveFits : minWidth ≤ cutoffWidth := (le_max_right m minWidth).trans (le_max_left ..)
  refine ⟨s₀,c,Q,K,cutoffWidth,pos,last,rfl,steps,injectionFits,le_max_right ..,nonempty,umin.trans reserveFits,innerPos,outerPos,
    small,travel,square,kpos,qpos,lanes,accurate,rounding,fun s later=>(rates K le_rfl s later).1,
    fun s later=>(rates K le_rfl s later).2,?_,innerPaid,paid⟩
  intro w size s later n coords bound
  exact replay w (reserveFits.trans size) s later n coords bound


end
end Hierarchy.ProtocolRAM.Calendar

end OAI
