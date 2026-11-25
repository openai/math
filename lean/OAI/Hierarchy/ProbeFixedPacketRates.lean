import OAI.Hierarchy.ProbeFixedPhase

namespace OAI
/-! # Per-shape funding, selector widths and quote precision on the original two catalogues -/

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage StripDirectory
open scoped Classical
noncomputable section
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

theorem local_funding {s : ℝ} (time : (v.finish:ℝ)/2 ≤ s) :
    (Fintype.card ((PayloadStrip.Columns (publicStages v.W) × Fin k) ⊕ PayloadStrip.Quotes (publicStages v.W) k):ℝ)/v.copyScale ≤ s*v.a*v.menu.margin ∧
    (Fintype.card ((ChainStrip.Columns v.depth × Fin k) ⊕ ChainStrip.Axes v.depth k):ℝ)/v.copyScale ≤ s*v.a*v.menu.margin ∧
    v.menu.margin≤v.payloadPackets.margin ∧ v.menu.margin≤v.boughtPackets.margin := by
  have funds := v.clock.funds s time
  have positive : 0≤(v.copyScale:ℝ) := Nat.cast_nonneg _
  exact ⟨(div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_max_left ..)) positive).trans funds,
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_max_right ..)) positive).trans funds,
    min_le_left ..,min_le_right ..⟩

/-- Both arities are paid at every actual scheduled date, including the first
half-temperature instant immediately after a purchase. -/
theorem native_funding (width phase attempt slice inner : ℕ) (date : phase≤v.mesh.inject+v.mesh.cool) :
    let p₀:=deadline v.mesh v.finish (v.basePhase width) (.outer phase attempt)
    let p₁:=deadline v.mesh v.finish (v.basePhase width) (.inner phase attempt slice inner)
    (Fintype.card ((PayloadStrip.Columns (publicStages v.W) × Fin k) ⊕ PayloadStrip.Quotes (publicStages v.W) k):ℝ)/
      v.copyScale≤p₀.time*p₀.a*v.menu.margin ∧
    (Fintype.card ((ChainStrip.Columns v.depth × Fin k) ⊕ ChainStrip.Axes v.depth k):ℝ)/
      v.copyScale≤p₁.time*p₁.a*v.menu.margin := by
  intro p₀ p₁
  have pos : 0<(v.finish:ℝ) := by exact_mod_cast v.clock.finish_pos
  have dates := v.real_times date
  have outer : (v.finish:ℝ)/2≤p₀.time := (by linarith : (v.finish:ℝ)/2≤v.finish).trans dates.1
  exact ⟨(v.local_funding outer).1,(v.local_funding (dates.2 slice)).2.1⟩

theorem payload_precision (j : v.payloadPackets.index) :
    (Fintype.card (PayloadRole (publicStages v.W) k):ℝ)*v.menu.maximum*(1/(v.precision:ℝ))≤
      (v.payloadPackets.packet j).width*v.menu.margin/2 := by
  have bound := v.clock.local_rounding (Sum.inl j) (Nat.zero_lt_of_lt (v.payloadPackets.wide j))
  apply le_trans _ bound
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_max_left ..))
    (Nat.cast_nonneg _)) (by positivity)

theorem bought_precision (j : v.boughtPackets.index) :
    (Fintype.card (PurchasedRole v.depth k):ℝ)*v.menu.maximum*(1/(v.precision:ℝ))≤
      (v.boughtPackets.packet j).width*v.menu.margin/2 := by
  have bound := v.clock.local_rounding (Sum.inr j) (Nat.zero_lt_of_lt (v.boughtPackets.wide j))
  apply le_trans _ bound
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_max_right ..))
    (Nat.cast_nonneg _)) (by positivity)

/-- Both the lower saving and the upper rate apply simultaneously to the exact
number of copies printed on every native row. The common bit floor is uniform. -/
theorem copied_widths (w : ℕ) (large : v.widthFloor≤w) :
    let B:=commonWidth v.menu.width
    2*(v.copyScale*B)≤w ∧ ∀j,
      2*(v.copyScale*B)*(v.menu.width j)≤w ∧
      copied (v.copyScale*B) (v.menu.width j) w≤v.menu.copiesAt v.copyScale w ∧
      v.menu.copiesAt v.copyScale w≤copied v.copyScale (v.menu.width j) w := by
  intro B
  have pos : 0<B := by unfold B commonWidth;omega
  have upper := v.clock.batch_width.trans large
  refine ⟨(Nat.le_mul_of_pos_right (2*(v.copyScale*B)) pos).trans upper,?_⟩
  intro j
  have width : 0<v.menu.width j := by
    cases j with
    | inl i => exact Nat.zero_lt_of_lt (v.payloadPackets.wide i)
    | inr i => exact Nat.zero_lt_of_lt (v.boughtPackets.wide i)
  exact ⟨(Nat.mul_le_mul_left _ (width_le_common v.menu.width j)).trans upper,
    v.menu.copy_bounds j v.copyScale w width v.clock.base_pos⟩


end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI
