import OAI.Computability.NearSquareRoot.InterchangeROMStageCompute
import OAI.Computability.NearSquareRoot.InterchangeROMStageTableEffective

/-! # Computable bounds over the finite rectangle stage

One coefficient bounds the number of ground slots at each bank boundary.
Another bounds the physical table factor at each of the five local matrix gates. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageVolume

open InterchangeROMStage InterchangeROMStageTable LoomRegisters

/-- Number of scalar rows in a single stage bank. -/
def slots (c : Parameters) (n : ℕ) : ℕ := (c.1.bank n).length*c.2.2.1

/-- A positive majorant computed from all twelve boundaries, including both ends. -/
def slotMax (c : Parameters) : ℕ := (∑ n : Fin 12, slots c n.val) + 1

/-- Time and space coefficient for a single generated literal matrix. -/
def gateFactor (c : Parameters) (tag : Fin 5) : ℕ :=
  let t := c.1.gate tag (inputBoundary tag)
  romPayloadFactor (t.2.1.length*c.2.2.1) (t.2.2.length*c.2.2.1) (bytes c t)

/-- A positive majorant computed from all five gate descriptions. -/
def gateMax (c : Parameters) : ℕ := (∑ tag : Fin 5, gateFactor c tag) + 1

theorem slots_le (c : Parameters) (n : Fin 12) : slots c n.val ≤ slotMax c :=
  le_trans (Finset.single_le_sum (f:=fun t : Fin 12 => slots c t)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ n)) (Nat.le_succ _)

theorem slots_le_any (c : Parameters) (n : ℕ) : slots c n ≤ slotMax c := by
  by_cases h : n < 12
  · exact slots_le c ⟨n,h⟩
  · obtain ⟨k,ek⟩ := Nat.exists_eq_add_of_le (show 11 ≤ n from by omega)
    rw [show n = k+11 from by omega]
    exact slots_le c ⟨11,by decide⟩

theorem gateFactor_le (c : Parameters) (tag : Fin 5) : gateFactor c tag ≤ gateMax c :=
  le_trans (Finset.single_le_sum (f:=gateFactor c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ tag))
    (Nat.le_succ _)

theorem slotMax_pos (c : Parameters) : 0 < slotMax c := Nat.zero_lt_succ _
theorem gateMax_pos (c : Parameters) : 0 < gateMax c := Nat.zero_lt_succ _

/-- Independent of address count, payload width and placement in the program. -/
theorem charge_le_factor (c : Parameters) (tag : Fin 5) (a w : ℕ) :
    charge c (c.1.gate tag (inputBoundary tag)) a w ≤ gateMax c * (a*(w+1)+1) :=
  Nat.mul_le_mul_right _ (gateFactor_le c tag)

private theorem primrec_finite_sum {X T : Type} [Primcodable X] (s : Finset T) (f : T → X → ℕ)
    (hf : ∀ t ∈ s, Primrec (f t)) : Primrec fun x => ∑ t ∈ s, f t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Primrec.const (α:=X) 0)
  | @insert a s ha ih =>
    have run := Primrec.nat_add.comp (hf a (Finset.mem_insert_self ..))
      (ih fun t ht => hf t (Finset.mem_insert_of_mem ht))
    simpa only [Finset.sum_insert ha] using run

theorem primrec_slots (n : ℕ) : Primrec fun c : Parameters => slots c n :=
  Primrec.nat_mul.comp (Primrec.list_length.comp (Frame.primrec_bank Primrec.fst n))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))

set_option maxHeartbeats 1600000 in
theorem primrec_gateFactor (tag : Fin 5) : Primrec fun c : Parameters => gateFactor c tag := by
  let args (c : Parameters) := (c,c.1.gate tag (inputBoundary tag))
  have ht : Primrec fun c : Parameters => c.1.gate tag (inputBoundary tag) :=
    Frame.primrec_gate Primrec.fst tag (inputBoundary tag)
  have pair : Primrec args := Primrec.id.pair ht
  let cost (z : Parameters × Frame.Table) := romPayloadFactor (z.2.2.1.length*z.1.2.2.1)
    (z.2.2.2.length*z.1.2.2.1) (bytes z.1 z.2)
  have hc : Primrec cost := primrec_factor
  exact (Primrec.comp (f:=cost) (g:=args) hc pair).of_eq (fun _ => rfl)

theorem primrec_slotMax : Primrec slotMax :=
  Primrec.succ.comp (primrec_finite_sum Finset.univ (fun n : Fin 12 => fun c => slots c n)
    (fun n _ => primrec_slots n))

theorem primrec_gateMax : Primrec gateMax :=
  Primrec.succ.comp (primrec_finite_sum Finset.univ (fun tag : Fin 5 => fun c => gateFactor c tag)
    (fun tag _ => primrec_gateFactor tag))

theorem computable_slotMax : Computable slotMax := primrec_slotMax.to_comp
theorem computable_gateMax : Computable gateMax := primrec_gateMax.to_comp

end InterchangeROMStageVolume

end NearSquareRoot
end Computability
end OAI
