import OAI.Hierarchy.ProbeFixedDiscrepancyCeilings
import OAI.Hierarchy.ProbeFixedStripCounts

namespace OAI
/-! # One height threshold for both modes' physical repair counters and score words -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- The same threshold works over all mounted layouts and every width at most
the size of the original row population. -/
theorem repair_word_room : ∀ᶠ z : ℕ in Filter.atTop,∀(P : v.Placement) (width : ℕ),width≤2^z →
    let W:=wordBits z (2^v.W) copies
    let H:=v.publicHeader P z width
    v.stripHeight≤z ∧ ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W ∧
      v.menu.alphabet<2^W ∧ v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width<2^W ∧
      H.payload.maxWord<2^W ∧ H.bought.maxWord<2^W := by
  let threshold:=⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊
  let K:=v.keepLimit+v.menu.maximum
  filter_upwards [Filter.eventually_ge_atTop v.stripHeight,Filter.eventually_ge_atTop threshold,
    Filter.eventually_ge_atTop v.menu.alphabet,Filter.eventually_ge_atTop K,v.discrepancy_word_room]
    with z late cut alpha large scores
  intro P width small W H
  have height : z<2^W := (Nat.lt_two_pow_self (n:=z)).trans_le
    (Nat.pow_le_pow_right (by decide) (by dsimp [W];rw [wordBits_linear];omega))
  have enough : K+1≤2^z := Nat.succ_le_of_lt (large.trans_lt (Nat.lt_two_pow_self (n:=z)))
  have bound:=append_room (h:=z) (d:=2^v.W) (copies:=copies) enough
  have copied : v.menu.copiesAt v.copyScale width≤2^z := (Nat.div_le_self ..).trans small
  have used : v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width≤K*2^z := by
    dsimp [K]
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ small) (Nat.mul_le_mul_left _ copied)
  exact ⟨late,cut.trans_lt height,alpha.trans_lt height,(used.trans (Nat.le_add_left ..)).trans_lt bound,
    scores P width⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
