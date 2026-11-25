import OAI.Computability.BorderVNP.CubeISAOwnedPacketCount
import OAI.Computability.BorderVNP.CubeISAOwnedSingletons

/-! # Charging the owned-row scanner to its physical packets and singleton bits

Every counter position costs its address preparation and branch overhead. The
callback is charged only at accepted positions. For packets the padded scan is
within a dimension-dependent factor of the physical row. For singletons the
outer scan has at most the squared label count of candidates and the inner bit
loop costs a constant per actual bit in the oriented row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.Owned

open Finset

variable {n d blocks : ℕ}

private theorem pairSquare (k : ℕ) : (k+2)*(k+2) ≤ 4*((k+2).choose 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    change (k+2+1)*(k+2+1) ≤ 4*((k+2+1).choose 2)
    rw [Nat.choose_succ_succ' (k+2) 1, Nat.choose_one_right]
    nlinarith

/-- At most four padded trials per strict symbol choice are needed in each
free coordinate. The orientation and block fields are already exact. -/
theorem packetTrials_le_four_pow_card (i : Fin (n+1)) (pair : Symbols d) :
    packetTrials n d blocks ≤ 4^n * Fintype.card {p : Packet n d blocks // p.1.1 i = pair} := by
  have hd : 2 ≤ d := by
    have h := pair.property
    have hb := pair.val.2.isLt
    change pair.val.1.val < pair.val.2.val at h
    omega
  have hpair := pairSquare (d-2)
  rw [Nat.sub_add_cancel hd] at hpair
  rw [packetTrials, card_packets_row]
  calc
    _ ≤ (4*d.choose 2)^n * 2 * blocks :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpair _))
    _ = _ := by rw [mul_pow]; ring

/-- Two independent tail labels range over at most the square of the full
product-label count. -/
theorem singlePairTrials_le_labels_sq (n d : ℕ) (hd : 0 < d) :
    singlePairTrials n d ≤ (d^(n+1))^2 := by
  have h : d^n ≤ d^(n+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ hd
  simpa only [singlePairTrials, pow_two] using Nat.mul_le_mul h h

/-- Split the variable-cost sum in the native `rowLoop_run` allowance into
one charge per counter and the callback sum over exactly the emitted counters. -/
theorem rowLoop_sum_le (N prep : ℕ) (emit : ℕ → Bool) (cost : ℕ → ℕ)
    (valid : Fin N → Prop) [DecidablePred valid] (he : ∀ t : Fin N, emit t.val = true ↔ valid t) :
    (∑ t ∈ range N, (prep+3 + if emit t then cost t else 1)) ≤
      N*(prep+4) + ∑ t : {t : Fin N // valid t}, cost t.val.val := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ ≤ ∑ t : Fin N, (prep+4 + if valid t then cost t.val else 0) := by
      apply sum_le_sum
      intro t _
      by_cases h : valid t
      · simp only [(he t).mpr h, ite_true, h]
        omega
      · have hf : emit t.val = false := Bool.eq_false_iff.mpr ((he t).not.mpr h)
        simp [h,hf]
    _ = _ := by
      rw [sum_add_distrib, ← sum_filter, ← sum_subtype_eq_sum_filter]
      simp

/-- The complete packet row loop, including its final guard, pays for the
actual callback at each uniquely represented packet. -/
theorem packet_rowLoop_budget (i : Fin (n+1)) (pair : Symbols d) (prep : ℕ)
    (emit : ℕ → Bool) (cost : ℕ → ℕ)
    (he : ∀ t : Fin (packetTrials n d blocks), emit t.val = true ↔ packetTrialValid t) :
    (∑ t ∈ range (packetTrials n d blocks), (prep+3 + if emit t then cost t else 1)) + 1 ≤
      4^n * Fintype.card {p : Packet n d blocks // p.1.1 i = pair} * (prep+4) +
        (∑ p : {p : Packet n d blocks // p.1.1 i = pair}, cost ((packetRowEquiv i pair).symm p).val.val) + 1 := by
  apply Nat.add_le_add_right
  refine (rowLoop_sum_le _ prep emit cost packetTrialValid he).trans ?_
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_right _ (packetTrials_le_four_pow_card i pair)
  · exact ((packetRowEquiv i pair).symm.sum_comp (fun t => cost t.val.val)).symm.le

/-- The inner bit loops at accepted pairs contribute exactly one copy of the
per-bit allowance for each singleton slot in the oriented physical row. -/
theorem singleScan_bit_sum (blocks width perBit : ℕ) (i : Fin (n+1)) (a b : Fin d) :
    (∑ _t : {t : Fin (singlePairTrials n d) // singleTrialValid i a b t}, blocks*width*perBit) =
      Fintype.card {z : SingleSlot n d blocks width // z.1.val.1 i = a ∧ z.1.val.2 i = b} * perBit := by
  rw [← Fintype.card_congr (singleOrderedEquiv blocks width i a b), Fintype.card_prod, Fintype.card_fin]
  simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, Nat.mul_assoc]

/-- For a singleton pair the bit loop uses two initial/final ticks and at
most `callback+2` per bit. Failed pairs incur only the outer scan overhead.
The last tick is the final row guard. -/
theorem single_rowLoop_budget (blocks width prep callback : ℕ) (i : Fin (n+1)) (a b : Fin d)
    (emit : ℕ → Bool) (cost : ℕ → ℕ)
    (he : ∀ t : Fin (singlePairTrials n d), emit t.val = true ↔ singleTrialValid i a b t)
    (hc : ∀ t : Fin (singlePairTrials n d), singleTrialValid i a b t →
      cost t.val ≤ 2 + blocks*width*(callback+2)) :
    (∑ t ∈ range (singlePairTrials n d), (prep+3 + if emit t then cost t else 1)) + 1 ≤
      (d^(n+1))^2 * (prep+6) +
        Fintype.card {z : SingleSlot n d blocks width // z.1.val.1 i = a ∧ z.1.val.2 i = b} *
          (callback+2) + 1 := by
  let T := {t : Fin (singlePairTrials n d) // singleTrialValid i a b t}
  have hT : Fintype.card T ≤ singlePairTrials n d := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (singleTrialValid i a b)
  have charge : (∑ t : T, cost t.val.val) ≤
      singlePairTrials n d * 2 +
      Fintype.card {z : SingleSlot n d blocks width // z.1.val.1 i = a ∧ z.1.val.2 i = b} * (callback+2) := by
    calc
      _ ≤ ∑ _t : T, (2 + blocks*width*(callback+2)) := sum_le_sum fun t _ => hc _ t.property
      _ = _ + _ := sum_add_distrib
      _ ≤ _ := Nat.add_le_add (by simpa using Nat.mul_le_mul_right 2 hT)
        (singleScan_bit_sum blocks width (callback+2) i a b).le
  apply Nat.add_le_add_right
  refine (rowLoop_sum_le _ prep emit cost (singleTrialValid i a b) he).trans ?_
  calc
    _ ≤ singlePairTrials n d * (prep+4) + _ := Nat.add_le_add_left charge _
    _ = singlePairTrials n d * (prep+6) + _ := by ring
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _
      (singlePairTrials_le_labels_sq n d (Nat.zero_lt_of_lt a.isLt))) _

end Cube.Physical.Owned

end BorderVNP
end Computability
end OAI
