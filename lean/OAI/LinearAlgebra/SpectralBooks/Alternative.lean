import OAI.LinearAlgebra.SpectralBooks.Selector
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Finset.Max

/-!
# Rational wire widths for a missing flat

In the proof of the characteristic-wise alternative, the compact space `X` is the spectrum,
`price e` is the normalized binary price of a candidate pair, and `crossing` is the log-price of
the crossing tensor. A pair witnessing a strict comparison may vary with the spectral point.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set Filter Topology

/-- Rationally reducing every upper wire width preserves the strict covering inequality on the
entire compact spectrum. The proof takes a neighborhood of the whole spectrum at scale one. -/
theorem exists_rational_wire_widths {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    (cap : E → ℝ) (hcap : ∀ e, 0 < cap e) (price : E → X → ℝ) (crossing : X → ℝ)
    (hprice : ∀ e, Continuous (price e)) (hcrossing : Continuous crossing)
    (hnonneg : ∀ e x, 0 ≤ price e x)
    (hstrict : ∀ x, ∃ e, crossing x < cap e * price e x) :
    ∃ w : E → ℚ, (∀ e, 0 < w e ∧ (w e : ℝ) < cap e) ∧
      ∀ x, ∃ e, crossing x < w e * price e x := by
  let U : Set (ℝ × X) := ⋃ e, {p | crossing p.2 < p.1 * cap e * price e p.2}
  have hU : IsOpen U := by
    refine isOpen_iUnion fun e ↦ isOpen_lt (hcrossing.comp continuous_snd) ?_
    exact (continuous_fst.mul continuous_const).mul ((hprice e).comp continuous_snd)
  have hone : ({1} : Set ℝ) ×ˢ (univ : Set X) ⊆ U := by
    rintro ⟨t, x⟩ ⟨(rfl : t = 1), -⟩
    obtain ⟨e, he⟩ := hstrict x
    exact mem_iUnion_of_mem e (by simpa using he)
  obtain ⟨u, v, hu, _, h1, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hU hone
  have hu' : u ∈ 𝓝[<] (1 : ℝ) := nhdsWithin_le_nhds (hu.mem_nhds (h1 rfl))
  obtain ⟨t, htu, ht0, ht1⟩ := Filter.nonempty_of_mem
    (inter_mem hu' (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)))
  have hbound (e) : t * cap e < cap e := mul_lt_of_lt_one_left (hcap e) ht1
  choose w hw using fun e ↦ exists_rat_btwn (hbound e)
  refine ⟨w, fun e ↦ ⟨?_, (hw e).2⟩, ?_⟩
  · exact_mod_cast (mul_pos ht0 (hcap e)).trans (hw e).1
  · intro x
    obtain ⟨e, he⟩ := mem_iUnion.mp (huv (mk_mem_prod htu (hv (mem_univ x))))
    exact ⟨e, he.trans_le (mul_le_mul_of_nonneg_right (hw e).1.le (hnonneg e x))⟩

/-- For finitely many pairs the rational choice saves the same positive amount of Euclidean
length on every pair, while still beating the crossing at every spectral point. -/
theorem exists_wire_length_saving {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [Fintype E] [Nonempty E] {D : ℕ} (hD : 0 < D) (len : E → ℝ)
    (hlen : ∀ e, 0 < len e) (price : E → X → ℝ) (crossing : X → ℝ)
    (hprice : ∀ e, Continuous (price e)) (hcrossing : Continuous crossing)
    (hnonneg : ∀ e x, 0 ≤ price e x)
    (hstrict : ∀ x, ∃ e, crossing x < (2 * D / len e) * price e x) :
    ∃ (w : E → ℚ) (γ : ℝ), 0 < γ ∧ (∀ e, 0 < w e ∧ (w e : ℝ) * len e ≤ 2 * D - γ) ∧
      ∀ x, ∃ e, crossing x < w e * price e x := by
  obtain ⟨w, hw, hcover⟩ := exists_rational_wire_widths (fun e ↦ 2 * D / len e)
    (fun e ↦ div_pos (by positivity) (hlen e)) price crossing hprice hcrossing hnonneg hstrict
  obtain ⟨a, _, ha⟩ := Finset.univ.exists_max_image (fun e ↦ (w e : ℝ) * len e)
    Finset.univ_nonempty
  refine ⟨w, 2 * D - w a * len a, sub_pos.mpr ((lt_div_iff₀ (hlen a)).mp (hw a).2),
    fun e ↦ ⟨(hw e).1, ?_⟩, hcover⟩
  simpa using ha e (Finset.mem_univ e)

/-- Starting with the pointwise ratio obstruction, choose a single bit width and a list of
integer-width wires covering the spectrum. For every comparison prefactor `K`, some power has
strictly smaller cost than the direct diameters, even after all summand indices are broadcast. -/
theorem exists_shorter_wire_products {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [Fintype E] [Nonempty E] {D : ℕ} (hD : 0 < D) (len : E → ℝ)
    (hlen : ∀ e, 0 < len e) (price : E → X → ℝ) (crossing : X → ℝ)
    (hprice : ∀ e, Continuous (price e)) (hcrossing : Continuous crossing)
    (hnonneg : ∀ e x, 0 ≤ price e x)
    (hstrict : ∀ x, ∃ e, crossing x < (2 * D / len e) * price e x) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : E → ℕ, (∀ e, 0 < b e) ∧
      (∀ x, ∃ e, m * crossing x < b e * price e x) ∧
      ∀ K : ℕ, 0 < K → ∃ j : ℕ, 0 < j ∧ ∃ budget : ℝ,
        (∀ edges : Fin j → E, ∑ i, b (edges i) * len (edges i) ≤ budget) ∧
        budget + 2 * D * Real.logb 2 ((K * Fintype.card E ^ j : ℕ) : ℝ) < 2 * D * m * j := by
  obtain ⟨w, γ, hγ, hw, hcover⟩ := exists_wire_length_saving hD len hlen price crossing
    hprice hcrossing hnonneg hstrict
  obtain ⟨m, hm, b, hb, _, hamp⟩ := exists_selector_format (D := D) w (fun e ↦ (hw e).1)
    (Fintype.card_pos (α := E)) hγ
  refine ⟨m, hm, b, fun e ↦ (hb e).1, ?_, ?_⟩
  · intro x
    obtain ⟨e, he⟩ := hcover x
    have heq : (b e : ℝ) = m * (w e : ℝ) := by exact_mod_cast (hb e).2
    refine ⟨e, ?_⟩
    rw [heq, mul_assoc]
    exact mul_lt_mul_of_pos_left he (by exact_mod_cast hm)
  · intro K hK
    obtain ⟨j, hj, hcost⟩ := hamp K hK
    refine ⟨j, hj, _, ?_, hcost⟩
    exact product_wire_cost_le (fun e ↦ scaled_wire_cost_le (hb e).2 (hw e).2)

end SpectralBooks
end LinearAlgebra
end OAI
