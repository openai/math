import OAI.Computability.BorderVNP.CubePackets

/-!
# Communication budget for the selected cube coordinate

Every padding slot in a full label pair appears in exactly one packet. Summing
Lemma 8.1 over the resulting packets and adding the singleton pairs gives (8.1)
for every choice of the local selectors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

/-- A packet's subcube, orientation, and consecutive block number. -/
abbrev Packet (n d blocks : ℕ) :=
  (((Fin (n+1) → Symbols d) × Bool) × Fin blocks)

/-- The number of padded slots over all ordered pairs of product labels. -/
def padded (n d blocks b : ℕ) := (blocks*b) * (d^(n+1))^2

/-- The packet incidences occupy at most all padded slots. -/
theorem packet_count (n d blocks b : ℕ) :
    Fintype.card (Packet n d blocks) * (2^n*b) ≤ padded n d blocks b := by
  classical
  have hi := Fintype.card_congr (packetEquiv n d blocks b)
  have cardTail : Fintype.card ((Fin n → Bool) × Fin b) = 2^n*b := by simp
  change _ = Fintype.card ((Packet n d blocks) × ((Fin n → Bool) × Fin b)) at hi
  rw [Fintype.card_prod (Packet n d blocks) _] at hi
  rw [cardTail] at hi
  rw [← hi]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h := Fintype.card_subtype_le (fun p : Label (n+1) d × Label (n+1) d ↦
    ∀ i, p.1 i ≠ p.2 i)
  change Fintype.card (FullPair (n+1) d) ≤ _ at h
  simpa only [padded, Label, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, sq, mul_comm]
    using Nat.mul_le_mul_right (blocks*b) h

/-- Total selected cube-edge width across one coordinate cut. -/
noncomputable def edgeLoad {n d blocks : ℕ} (w : Packet n d blocks → Edge (n+1) → ℝ)
    (i : Fin (n+1)) := ∑ p, ∑ x : Vertex (n+1), w p (x,i)

/-- The contribution of the singleton wires to a coordinate's crossing width. -/
def singletonLoad (n d blocks b : ℕ) (i : Fin (n+1)) : ℕ :=
  ∑ u : Label (n+1) d, (blocks*b) * ((singletons u).filter fun v ↦ u i ≠ v i).card

/-- The global cut and selector budget (8.1), for the actual enumerated packets and
singleton pairs. The two per-packet hypotheses are exactly the bounds of Lemma 8.1. -/
theorem coordinate_budget (n d blocks b : ℕ) (hd : 0 < d) {η : ℝ} (hη : 0 ≤ η)
    (w : Packet n d blocks → Edge (n+1) → ℝ) (sel : Packet n d blocks → ℝ)
    (hw : ∀ p, ∑ e, w p e ≤ 2*2^n*Real.sqrt (n+1)*b)
    (hs : ∀ p, sel p ≤ η*b) :
    ∃ i, (∀ j, edgeLoad w i + singletonLoad n d blocks b i ≤
        edgeLoad w j + singletonLoad n d blocks b j) ∧
      edgeLoad w i + singletonLoad n d blocks b i + ∑ p, sel p ≤
        padded n d blocks b * (2/Real.sqrt (n+1) + (n+1)/d + η) := by
  have packetBits : (Fintype.card (Packet n d blocks) : ℝ) * (2^n*b) ≤ padded n d blocks b :=
    by exact_mod_cast packet_count n d blocks b
  have edgeSum : (∑ i, edgeLoad w i) ≤ 2 * Real.sqrt (n+1) * padded n d blocks b := by
    unfold edgeLoad
    rw [Finset.sum_comm]
    simp_rw [← Fintype.sum_prod_type_right]
    apply (Finset.sum_le_sum fun p _ ↦ hw p).trans
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ = 2 * Real.sqrt (n+1) * ((Fintype.card (Packet n d blocks) : ℝ) * (2^n*b)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left packetBits (by positivity)
  have single (i : Fin (n+1)) : (singletonLoad n d blocks b i : ℝ) ≤
      padded n d blocks b * ((n+1)/(d : ℝ)) := by
    unfold singletonLoad
    rw [Nat.cast_sum]
    apply (Finset.sum_le_sum (fun u _ ↦ ?_)).trans
      (by simpa only [Nat.cast_add, Nat.cast_one, padded] using singleton_fraction n d (blocks*b) hd)
    exact_mod_cast Nat.mul_le_mul_left (blocks*b) (Finset.card_filter_le _ _)
  have selectors : (∑ p, sel p) ≤ padded n d blocks b * η := by
    apply (Finset.sum_le_sum (fun p _ ↦ hs p)).trans
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hone : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hb : (b:ℝ) ≤ 2^n*b := le_mul_of_one_le_left (Nat.cast_nonneg b) hone
    calc
      _ = (Fintype.card (Packet n d blocks) : ℝ) * b * η := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)).trans packetBits) hη
  exact minimizing_coordinate (edgeLoad w) (fun i ↦ singletonLoad n d blocks b i)
    edgeSum single selectors

end Cube

end BorderVNP
end Computability
end OAI
