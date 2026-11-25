import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordPeeling
import OAI.LinearAlgebra.SpectralBooks.ChordGraph.NoPlaneChordPacket
import OAI.LinearAlgebra.SpectralBooks.StraighteningCount
import OAI.LinearAlgebra.SpectralBooks.ClassComparison

/-!
# Straightening a graph of wires in cyclic order

Choose a packet width for each of the finitely many alternating quadruples.
While two crossing chords carry a packet, straighten it. The sum of the two
cyclic arc lengths' products, weighted by the bit widths, drops by at least
the packet width in each branch. Expanding the bounded-width remainder
costs a constant depending only on the number of sites and the tolerance.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped BigOperators Classical
noncomputable section

namespace ChordGraph

open SiteTensor

variable {k : ℕ} {K : Type*} [Field K] [Nonempty (Fin k)]

/-- Four distinct polygon vertices listed in cyclic order. -/
abbrev Quad (k : ℕ) :=
  {p : Fin k × Fin k × Fin k × Fin k // p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2}

/-- The direct-sum class comparison for an arbitrary integer-width wiring.
The exponent has the specified slope for *every* graph, with an additive
constant independent of its widths. -/
theorem straighten_classes (hpacket : ∀ (q : Quad k) (σ : ℝ), 0 < σ →
      HasWirePacket K q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 σ)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, ∀ g : Widths k, ∃ (L : ℕ) (terms : Fin L → Widths k),
      (L:ℝ) ≤ (2:ℝ)^(η * total g + C) ∧
      (∀ l, Noncrossing (terms l) ∧ ∀ i, load i (terms l) ≤ load i g) ∧
      graphClass K g ≤ ∑ l, graphClass K (terms l) := by
  classical
  let M : ℕ := k*k+1
  let σ := η / M
  have hM : (0:ℝ) < (M:ℝ) := by dsimp [M]; positivity
  have hσ : 0 < σ := div_pos hη hM
  choose m hm L hL u v huv hcomp using fun q : Quad k =>
    chord_packet_of_wire_packet K q.property.1 q.property.2.1 q.property.2.2 (hpacket q σ hσ)
  let B := ∑ q, m q
  let C := Fintype.card (Chord k) * B
  refine ⟨C, fun g => ?_⟩
  let bounded (y x : Widths k) := ∀ i, load i y ≤ load i x
  have expand (x : Widths k) :
      (∃ (L : ℕ) (t : Fin L → Widths k), (L:ℝ) ≤ (2:ℝ)^(C:ℝ) ∧
        (∀ j, Noncrossing (t j) ∧ bounded (t j) x) ∧ graphClass K x ≤ ∑ i, graphClass K (t i)) ∨
      (∃ d : ℕ, 0 < d ∧ ∃ (L : ℕ) (t : Fin L → Widths k), (L:ℝ) ≤ (2:ℝ)^(σ*d) ∧
        (∀ j, potential (t j) + d ≤ potential x ∧ bounded (t j) x) ∧
        graphClass K x ≤ ∑ i, graphClass K (t i)) := by
    by_cases done : ∀ {a b c d : Fin k} (hab : a < b) (hbc : b < c) (hcd : c < d),
        ¬(B ≤ x (edge a c (hab.trans hbc)) ∧ B ≤ x (edge b d (hbc.trans hcd)))
    · left
      obtain ⟨s,b,hx,hsmall,hgood,hload⟩ := split_of_no_large_crossing x B done
      refine ⟨2^total s, fun _ => b, ?_, fun _ => ⟨hgood, hload⟩, ?_⟩
      · rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
        exact pow_le_pow_right₀ (by norm_num) hsmall
      · rw [hx, graphClass_add]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
          Nat.cast_ofNat]
        apply mul_mono _ le_rfl
        simpa using graphClass_le K s
    · right
      push Not at done
      obtain ⟨a,b,c,d,hab,hbc,hcd,hac,hbd⟩ := done
      let q : Quad k := ⟨(a,b,c,d),hab,hbc,hcd⟩
      have hwidth : m q ≤ B := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q)
      obtain ⟨r, hr⟩ := exists_peel_crossing x hab hbc hcd (m q)
        (hwidth.trans hac) (hwidth.trans hbd)
      let child (j : Fin (L q)) := r + (u q j • parallel hab hbc hcd + v q j • nested hab hbc hcd)
      refine ⟨m q, hm q, L q, child, hL q, fun j => ⟨?_, ?_⟩, ?_⟩
      · have hu := Nat.mul_le_mul_left (u q j) (potential_parallel_lt_crossing hab hbc hcd)
        have hv := Nat.mul_le_mul_left (v q j) (potential_nested_lt_crossing hab hbc hcd)
        rw [hr]
        simp only [child, map_add, map_nsmul, nsmul_eq_mul]
        rw [← huv q j]
        nlinarith only [hu,hv]
      · intro i
        rw [hr]
        simp only [child, map_add, map_nsmul, nsmul_eq_mul, load_parallel_eq_crossing,
          load_nested_eq_crossing, ← huv q j]
        simp [add_mul]
      · rw [hr, graphClass_add]
        calc
          _ ≤ graphClass K r * ∑ j, graphClass K
              (u q j • parallel hab hbc hcd + v q j • nested hab hbc hcd) :=
            mul_mono le_rfl (hcomp q)
          _ = _ := by simp [Finset.mul_sum, child]
  obtain ⟨n, terms, hn, hgood, hc⟩ := straightening_count_of_steps (graphClass K) potential
    Noncrossing bounded (fun h g i => (h i).trans (g i)) hσ.le expand g
  refine ⟨n, terms, hn.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_), hgood, hc⟩
  apply add_le_add_left
  calc
    σ * (potential g : ℝ) ≤ σ * ((M:ℝ) * (total g:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hσ.le
      exact_mod_cast (potential_le_total g).trans (Nat.mul_le_mul_right (total g) (by dsimp [M]; omega))
    _ = _ := by dsimp [σ]; field_simp

/-- Apply the local restricting maps to obtain the actual ordinary coefficient
sum in any given representative. No local coordinate outside the polygon
may be changed jointly with another site. -/
theorem straighten_in_format (hpacket : ∀ (q : Quad k) (σ : ℝ), 0 < σ →
      HasWirePacket K q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 σ)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, ∀ (g : Widths k) (R : Raw.{0} (Fin k) K), ofRaw R = graphClass K g →
      ∃ (L : ℕ) (terms : Fin L → Widths k) (z : Fin L → (∀ i, R.Leg i) → K),
        (L:ℝ) ≤ (2:ℝ)^(η * total g + C) ∧ R.coeff = ∑ l, z l ∧
        ∀ l, Noncrossing (terms l) ∧ (∀ i, load i (terms l) ≤ load i g) ∧
          ofRaw {R with coeff := z l} ≤ graphClass K (terms l) := by
  obtain ⟨C, hC⟩ := straighten_classes hpacket hη
  refine ⟨C, fun g R hR => ?_⟩
  obtain ⟨L, terms, hL, hterms, hsum⟩ := hC g
  obtain ⟨z, hz, hle⟩ := images_of_le_sum R _ (hR.le.trans hsum)
  exact ⟨L, terms, z, hL, hz, fun l => ⟨(hterms l).1, (hterms l).2, hle l⟩⟩

/-- Tree-side straightening over the ground field, stated with the actual
ordinary sum in the chosen local coordinate spaces. -/
theorem straighten_of_no_plane
    (noPlane : ¬ Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2)))) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, ∀ (g : Widths k) (R : Raw.{0} (Fin k) K), ofRaw R = graphClass K g →
      ∃ (L : ℕ) (terms : Fin L → Widths k) (z : Fin L → (∀ i, R.Leg i) → K),
        (L:ℝ) ≤ (2:ℝ)^(η * total g + C) ∧ R.coeff = ∑ l, z l ∧
        ∀ l, Noncrossing (terms l) ∧ (∀ i, load i (terms l) ≤ load i g) ∧
          ofRaw {R with coeff := z l} ≤ graphClass K (terms l) :=
  straighten_in_format (fun q _ hσ =>
    exists_wire_packet_of_no_plane noPlane q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 hσ) hη

end ChordGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
