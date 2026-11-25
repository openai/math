import OAI.ThreeFlat.Diagonal.TracePublicMemoryControls
import OAI.ThreeFlat.Diagonal.TraceStaticMemoryInput
import OAI.ThreeFlat.Diagonal.TraceUniformMemoryCircuit

namespace OAI
/-! # A common gate table for all physical memory rows -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open Computability.VPVNP BurstRAM TraceRows TraceCompose

variable {w r S f d : ℕ}

private noncomputable def feed (hw : 3 ≤ w+1) :
    TraceMemoryCircuit.ControlledPort d (w+1) → Packet (LocalPort w r d ⊕ MemoryControl w d)
  | .inl a => staticInput hw a
  | .inr c => read (.inr (.inr c))

/-- One Boolean circuit for the memory check, with row dependence confined to public input pins. -/
noncomputable def staticMemory (hw : 3 ≤ w+1) : Packet (LocalPort w r d ⊕ MemoryControl w d) :=
  substituteFintype (feed hw) ((TraceMemoryCircuit.uniformRow (d := d) (by omega : 2 ≤ w+1)).circuit ())

theorem staticMemory_eval (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) (x : LocalPort w r d → Bool) :
    (staticMemory hw).2.eval (Sum.elim x (memoryControlAt hw hs hf v)) =
      (memoryPacket hw hs hf v).2.eval x := by
  rw [staticMemory,substituteFintype_eval,memoryPacket_eval]
  let bits := fun a => (memoryInput hw hs hf v a).2.eval x
  have h : (fun i => (feed hw i).2.eval (Sum.elim x (memoryControlAt hw hs hf v))) =
      Sum.elim bits (TraceMemoryCircuit.controlsAt v) := by
    funext i
    cases i with
    | inl a => exact staticInput_eval hw hs hf v x (TraceMemoryCircuit.controlsAt v) a
    | inr c => rfl
  rw [h]
  exact TraceMemoryCircuit.uniformRow_eval (by omega) v bits

theorem staticMemory_size (hw : 3 ≤ w+1) :
    (staticMemory (r := r) (d := d) hw).1 ≤ 90000*(d+2)^2*(w+2)^2 := by
  classical
  let inp := feed (r := r) (d := d) hw
  have hin : (∑ i : TraceMemoryCircuit.ControlledPort d (w+1), (inp i).1) ≤
      (14*(w+1))*(560*(w+2)) := by
    rw [Fintype.sum_sum_type]
    have hz : (∑ c : TraceMemoryCircuit.MemoryControl d (w+1), (inp (.inr c)).1) = 0 := by
      apply Finset.sum_eq_zero
      exact fun _ _ => rfl
    rw [hz,add_zero,Fintype.sum_sum_type]
    have he : (∑ i, (inp (.inl (.inr i))).1) = 0 := by
      apply Finset.sum_eq_zero
      rintro (⟨l,own,s,g,j⟩ | ⟨out,g,j⟩) _
      all_goals rfl
    rw [he,add_zero]
    calc
      _ ≤ ∑ _ : Fin 2 × Fin 7 × Fin (w+1), 560*(w+2) :=
        Finset.sum_le_sum fun i _ => staticInput_size hw (.inl i)
      _ = _ := by simp; ring
  rw [staticMemory, substituteFintype_size]
  have hrow := TraceMemoryCircuit.uniformRow_size (d := d) (by omega : 2 ≤ w+1)
  apply (Nat.add_le_add hin hrow).trans
  nlinarith only [Nat.zero_le (d^2*w^2),Nat.zero_le (d^2*w),Nat.zero_le (d*w^2),
    Nat.zero_le (d*w),Nat.zero_le d,Nat.zero_le w,Nat.zero_le (d^2),Nat.zero_le (w^2)]

end ThreeFlat.Diagonal.TraceRowPackets

end OAI
