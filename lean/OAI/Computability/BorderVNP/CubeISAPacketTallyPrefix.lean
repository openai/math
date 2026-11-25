import OAI.Computability.BorderVNP.CubeISAPacketTally
import OAI.Computability.BorderVNP.CubeISAOwnedRows

/-! # Actual crossing contributions over prefixes of the owned packet scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.PacketTally

open Physical Physical.Owned Finset

variable {n d blocks : ℕ}

/-- One contribution at a mixed-radix counter. Skipped counters contribute zero. -/
def atTrial (i : Fin (n+1)) (sym : Symbols d) (f : Packet n d blocks → Fin (n+1) → ℕ)
    (k : ℕ) (j : Fin (n+1)) : ℕ :=
  if hk : k < packetTrials n d blocks then
    ((packetTrial i sym ⟨k,hk⟩).map (fun p => f p j)).getD 0
  else 0

/-- Sum at one direction after scanning a prefix of the local candidates. -/
def rowPrefix (i : Fin (n+1)) (sym : Symbols d) (f : Packet n d blocks → Fin (n+1) → ℕ)
    (k : ℕ) (j : Fin (n+1)) : ℕ := ∑ t ∈ range k, atTrial i sym f t j

/-- At a valid counter the new summand is precisely the associated physical packet. -/
theorem prefix_valid (i : Fin (n+1)) (sym : Symbols d) (f : Packet n d blocks → Fin (n+1) → ℕ)
    (t : Fin (packetTrials n d blocks)) (good : packetTrialValid t) (j : Fin (n+1)) :
    rowPrefix i sym f (t.val+1) j = rowPrefix i sym f t.val j + f (packetRowEquiv i sym ⟨t,good⟩).val j := by
  simp [rowPrefix,sum_range_succ,atTrial,t.isLt,packetTrial,good]

/-- The row receives no update at a rejected mixed-radix candidate. -/
theorem prefix_skip (i : Fin (n+1)) (sym : Symbols d) (f : Packet n d blocks → Fin (n+1) → ℕ)
    (t : Fin (packetTrials n d blocks)) (bad : ¬packetTrialValid t) (j : Fin (n+1)) :
    rowPrefix i sym f (t.val+1) j = rowPrefix i sym f t.val j := by
  simp [rowPrefix,sum_range_succ,atTrial,t.isLt,packetTrial,bad]

/-- All visited packets together give the physical sum over the one owned unordered row. -/
theorem prefix_full (i : Fin (n+1)) (sym : Symbols d) (f : Packet n d blocks → Fin (n+1) → ℕ)
    (j : Fin (n+1)) :
    rowPrefix i sym f (packetTrials n d blocks) j = ∑ p : {p : Packet n d blocks // p.1.1 i = sym}, f p.val j := by
  let val (t : Fin (packetTrials n d blocks)) := atTrial i sym f t.val j
  calc
    _ = ∑ t : Fin (packetTrials n d blocks), val t := (Fin.sum_univ_eq_sum_range ..).symm
    _ = ∑ t, if packetTrialValid t then val t else 0 := sum_congr rfl fun t _ => by
      by_cases ht : packetTrialValid t <;> simp [ht,val,atTrial,packetTrial]
    _ = ∑ t : {t : Fin (packetTrials n d blocks) // packetTrialValid t}, val t.val := by
      rw [← sum_filter, sum_subtype (p := packetTrialValid) (univ.filter packetTrialValid) (fun _ => by simp) val]
    _ = _ := Fintype.sum_equiv (packetRowEquiv i sym) _ _ fun t => by
      simp [val,atTrial,packetTrial,t.property]

/-- The true physical crossing width from a valid selector, in any coordinate,
is at most the number of edge slots times the edge width. -/
theorem contribution_le (K h b s : ℕ) (mem : ℕ → ℕ) (base : ℕ) (p : Packet n d blocks) (j : Fin (n+1)) :
    contribution K h b s mem base p j ≤ h*s := by
  unfold contribution
  split
  · omega
  · rw [RowAccum.packet_direction_sum]
    simpa using (sum_le_sum (s := (univ : Finset (Fin h))) (g := fun _ => s) (fun k _ =>
      show (if _ then s else 0) ≤ s by split <;> omega))

/-- A public per-packet width bound limits every intermediate row count. -/
theorem prefix_le (i : Fin (n+1)) (sym : Symbols d) (f : Packet n d blocks → Fin (n+1) → ℕ)
    (B : ℕ) (bound : ∀ p j, f p j ≤ B) (k : ℕ) (j : Fin (n+1)) :
    rowPrefix i sym f k j ≤ k*B := by
  have point (t : ℕ) : atTrial i sym f t j ≤ B := by
    unfold atTrial
    split
    · cases packetTrial i sym _ with
      | none => simp
      | some p => exact bound p j
    · omega
  simpa [rowPrefix] using (sum_le_sum (s := range k) (g := fun _ => B) (fun t _ => point t))

end Cube.PacketTally

end BorderVNP
end Computability
end OAI
