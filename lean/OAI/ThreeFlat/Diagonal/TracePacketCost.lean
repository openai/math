import OAI.ThreeFlat.Diagonal.TraceMemoryPacketInputs

namespace OAI
/-! # Resource bound for a physical memory-check packet -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open Computability.VPVNP BurstRAM TraceRows TraceCompose
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w r f S d : ℕ}

private theorem headerExpr_size (s : Fin 2) (k : Fin (w+1)) :
    (headerExpr (r := r) (d := d) s k).size ≤ 1 := by
  induction k using Fin.lastCases <;> simp [headerExpr, Expr.size]

theorem memoryInput_size (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) (a : TraceMemoryCircuit.Port d (w+1)) :
    (memoryInput (r := r) hw hs hf v a).1 ≤ 224*(w+2) := by
  rcases a with ⟨s,g,j⟩ | (⟨l,own,s,g,j⟩ | ⟨out,g,j⟩)
  · by_cases hi : slotAddress d v s < S
    · simp only [memoryInput, dite_eq_left hi]
      apply (TracePair.formulaPacket_size_le _).trans
      let a : Word (w+1) := TraceBanks.wide (⟨slotAddress d v s, hi.trans_le hs⟩ : Word w)
      have h := initKey_size a (headerExpr (r := r) (d := d) s)
        (headerExpr_size s) g j
      apply (Nat.mul_le_mul_left 4 h).trans
      omega
    · by_cases hstep : slotAddress d v s-S < f
      · simp only [memoryInput, dite_eq_right hi, dite_eq_left hstep]
        apply (TracePair.formulaPacket_size_le _).trans
        let t : Word (w+1) := ⟨slotAddress d v s-S,hstep.trans_le hf⟩
        have h := probeKey_size hw (cpuExpr (r := r) (d := d) s.castSucc) t
          (fun _ => by rfl) g j
        exact (Nat.mul_le_mul_left 4 h).trans (by omega)
      · simp only [memoryInput, dite_eq_right hi, dite_eq_right hstep]
        exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- Only the first fourteen words emit input gates. All cross-layer and
boundary inputs are wire references to previously placed bits. -/
theorem memoryPacket_size (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) :
    (memoryPacket (r := r) hw hs hf v).1 ≤ 44000*(d+2)^2*(w+2)^2 := by
  classical
  let inp := memoryInput (r := r) hw hs hf v
  have hin : (∑ i : TraceMemoryCircuit.Port d (w+1), (inp i).1) ≤
      (14*(w+1))*(224*(w+2)) := by
    rw [Fintype.sum_sum_type]
    have hz : (∑ i, (inp (.inr i)).1) = 0 := by
      apply Finset.sum_eq_zero
      rintro (⟨l,own,s,g,j⟩ | ⟨out,g,j⟩) _
      all_goals rfl
    rw [hz, add_zero]
    calc
      _ ≤ ∑ _ : Fin 2 × Fin 7 × Fin (w+1), 224*(w+2) :=
        Finset.sum_le_sum fun i _ => memoryInput_size hw hs hf v (.inl i)
      _ = _ := by simp; ring
  rw [memoryPacket, substituteFintype_size]
  have hrow := TraceMemoryCircuit.row_size (show 2 ≤ w+1 by omega) v
  have h := Nat.add_le_add hin hrow
  apply h.trans
  nlinarith only [Nat.zero_le (d^2*w^2), Nat.zero_le (d^2*w), Nat.zero_le (d*w^2),
    Nat.zero_le (d*w), Nat.zero_le d, Nat.zero_le w, Nat.zero_le (d^2), Nat.zero_le (w^2)]

end ThreeFlat.Diagonal.TraceRowPackets

end OAI
