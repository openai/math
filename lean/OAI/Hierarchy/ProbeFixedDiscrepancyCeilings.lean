import OAI.Hierarchy.ProbeFixedRowPages

namespace OAI
/-! # Height-independent bounds on both tables of printed discrepancy scores -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StripDirectory
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def payloadWordCeiling (N : ℕ) :=
  Finset.univ.sup (AttemptGate.discrepancyWord F (PayloadStrip.wires N k) (PayloadStrip.demands N k)
    (fun key=>PayloadStrip.prices N k v.radius (payloadGrid v.digitRadix v.precision key)) v.precision)

def purchasedWordCeiling :=
  Finset.univ.sup (AttemptGate.discrepancyWord F (ChainStrip.wires v.depth k) (ChainStrip.demands v.depth k)
    (fun key=>ChainStrip.prices v.depth k v.radius (gridAxes v.digitRadix v.precision key)) v.precision)

/-- Only the public precision and radius enter the score values. Their ordinal ranges do
not vary with the layout, the amount of stock, the transaction date, or the payload width. -/
theorem discrepancy_word_room :
    ∀ᶠ z : ℕ in Filter.atTop, ∀(P : v.Placement) (width : ℕ),
    let H:=v.publicHeader P z width
    let w:=wordBits z (2^v.W) copies
    H.payload.maxWord<2^w ∧ H.bought.maxWord<2^w := by
  filter_upwards [Filter.eventually_ge_atTop (max (v.payloadWordCeiling (publicStages v.W)) v.purchasedWordCeiling)] with z large
  intro P width H w
  let N:=Stages z (2^v.W)
  have fixed : N=publicStages v.W:=fixed_stage_count z v.W
  have wide : z<2^w := (Nat.lt_two_pow_self (n:=z)).trans_le
    (Nat.pow_le_pow_right (by decide) (by dsimp [w];rw [wordBits_linear];omega))
  constructor
  · apply lt_of_le_of_lt _ wide
    apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro key _
    rw [v.payload_vector_word P z width u key]
    have price := funext (v.payload_page_grid z width u)
    rw [price]
    exact (Finset.le_sup (Finset.mem_univ key) : _≤v.payloadWordCeiling N).trans
      (by rw [fixed];exact (le_max_left ..).trans large)
  · apply lt_of_le_of_lt _ wide
    apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro key _
    rw [v.purchased_vector_word P z width u key]
    have price:=funext (v.purchased_page_grid width u)
    rw [price]
    exact (Finset.le_sup (Finset.mem_univ key) : _≤v.purchasedWordCeiling).trans ((le_max_right ..).trans large)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
