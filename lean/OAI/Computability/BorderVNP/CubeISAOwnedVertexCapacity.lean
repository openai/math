import OAI.Computability.BorderVNP.CubeISAOwnedVertexFold

/-! # Exact capacity of the owned vertex directory

The cursor charges only valid packet trials. At the end of the row the
number of charged packets is precisely the physical strict-pair count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedVertex

open Cube Cube.Physical Cube.Physical.Owned Finset

variable {n d blocks : ℕ}

/-- Number of physically selected packets before a local counter. -/
def selectedPrefix (i : Fin (n+1)) (pair : Symbols d) (k : ℕ) : ℕ :=
  ∑ j ∈ range k, (packetAtNat (blocks := blocks) i pair j).isSome.toNat

/-- The cursor reflects precisely the emitted triples at every intermediate trial. -/
theorem rowImage_cursor (i : Fin (n+1)) (pair : Symbols d) (high : Bool) (base stride width out : ℕ)
    (initial : ℕ → ℕ) (k : ℕ) :
    (rowImage (blocks := blocks) i pair high base stride width out initial k).1 =
      out + selectedPrefix (blocks := blocks) i pair k * (3*2^n) := by
  induction k with
  | zero => simp [rowImage, selectedPrefix]
  | succ k ih =>
    rw [rowImage]
    have hs : selectedPrefix (blocks := blocks) i pair (k+1) =
        selectedPrefix (blocks := blocks) i pair k + (packetAtNat (blocks := blocks) i pair k).isSome.toNat :=
      sum_range_succ ..
    rw [hs]
    cases h : packetAtNat (blocks := blocks) i pair k with
    | none => simpa using ih
    | some p => simp [appendPacket,ih,Nat.add_mul,Nat.add_assoc]

/-- The final number of selected packets equals the explicit physical row cardinality. -/
theorem selectedPrefix_end (i : Fin (n+1)) (pair : Symbols d) :
    selectedPrefix (blocks := blocks) i pair (packetTrials n d blocks) = 2*blocks*(d.choose 2)^n := by
  unfold selectedPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  have part (t : Fin (packetTrials n d blocks)) :
      (packetAtNat (blocks := blocks) i pair t.val).isSome.toNat = if packetTrialValid t then 1 else 0 := by
    by_cases h : packetTrialValid t <;> simp [packetAtNat,packetTrial,t.isLt,h]
  simp_rw [part]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← Fintype.card_subtype]
  exact (Fintype.card_congr (packetRowEquiv i pair)).trans (card_packets_row i pair)

/-- Any one selected packet and all earlier output records fit inside the
exact row-sized buffer. -/
theorem selectedPrefix_capacity (i : Fin (n+1)) (pair : Symbols d)
    (t : Fin (packetTrials n d blocks)) (h : packetTrialValid t) :
    selectedPrefix (blocks := blocks) i pair t.val + 1 ≤ 2*blocks*(d.choose 2)^n := by
  rw [← selectedPrefix_end i pair]
  have e : selectedPrefix (blocks := blocks) i pair (t.val+1) =
      selectedPrefix (blocks := blocks) i pair t.val + 1 := by
    unfold selectedPrefix
    rw [sum_range_succ, (selected_fields i pair t h).1]
    rfl
  rw [← e]
  apply sum_le_sum_of_subset_of_nonneg (range_mono t.isLt)
  exact fun _ _ _ => Nat.zero_le _

end RoutingISA.OwnedVertex

end BorderVNP
end Computability
end OAI
