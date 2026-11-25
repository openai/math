import OAI.Computability.NearSquareRoot.FixedCandidateCRTCloth
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepBatches

/-! # Running complete CRT passes from native record-permutation kernels -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code FixedPoint DigitPacking Space

private theorem elem_size_le {A : Type} [Codec A] (l : List A) {a : A} (h : a ∈ l) : size a ≤ size l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    rw [size_cons]
    rcases List.mem_cons.mp h with rfl | tail
    · omega
    · exact (ih tail).trans (by omega)

variable {I : Type} (n : I → ℕ) (inv : Bool)

/-- The complete header reaching any one half-stage has size polynomial in address bits. -/
theorem seedSizeDom : Dom (fun p : Input n inv => addressBits (n p.1)) (fun p => size (seed inv p.2.1.val)) := by
  let bits (p : Input n inv) := addressBits (n p.1)
  have tiny : Dom bits (fun p => size (tally (bits p))) := ⟨1,3,by intro p; simp [size_tally]; omega⟩
  apply ((seeds_poly inv).length.map (fun p => tally (bits p)) |>.sub tiny).mono
  intro p
  apply elem_size_le
  simpa [bits,seeds_eq] using List.mem_map_of_mem (f := seed inv) p.2.1.property

/-- Any polynomial setup allowance for these small headers fits linearly in the original operand. -/
theorem setupCap {J : Type} {n : J → ℕ} (hn : ∀ i, 2 ≤ n i)
    (t : J → ℕ) (d : Dom (fun i => addressBits (n i)) t) : ∃ C : ℕ, ∀ i, t i ≤ C*(n i+1) := by
  obtain ⟨B,hB⟩ := setup_le_array d
  refine ⟨B*192,fun i => (hB i).trans ?_⟩
  have vol := array_volume (hn i)
  have cap : 2^(addressBits (n i)) ≤ 192*(n i+1) :=
    (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)).trans
      (vol.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))))
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ cap

noncomputable section

variable (hs : ∀ i, Directory (n i))

/-- Keep the depth-dependent packed address space entirely inside the stage interpreter. -/
def packedRows {n : ℕ} (h : Directory n) (s : Switch n) (v : Packed n s → Record (addressBits n)) :=
  send ((records (v ∘ packing h s)).map Dusk.tie)

theorem packedRows_pack {n : ℕ} (h : Directory n) (s : Switch n) (r : Array n) :
    packedRows h s (pack h s r) = send ((records r).map Dusk.tie) := by
  unfold packedRows
  congr 3
  funext j
  simp [pack]

theorem packedRows_scatter {n : ℕ} (h : Directory n) (inv : Bool) (s : Switch n) (r : Array n) :
    packedRows h s (Benes.scatter (packedSlot h inv s) (pack h s r)) =
      send ((records (step h inv r s)).map Dusk.tie) := rfl

set_option maxHeartbeats 1600000 in
/-- Translate the actual packed-stage task boundary to the fixed candidate, then run every
depth in the generated order. None of the record values enter the finite program. -/
theorem nativeSweep (hn : ∀ i, 2 ≤ n i) (t : ℕ → ℕ)
    (native : BoundedTask (fun p : Input n inv => t (n p.1)) (fun p => n p.1)
      (fun p => .fork (send (seed inv p.2.1.val)) (packedRows (hs p.1) p.2.1.val (pack (hs p.1) p.2.1.val p.2.2)))
      (fun p => packedRows (hs p.1) p.2.1.val
        (Benes.scatter (packedSlot (hs p.1) inv p.2.1.val) (pack (hs p.1) p.2.1.val p.2.2)))) :
    StreamPass n (fun u => count u*(t u+u)+u) (fun i => outcome (hs i) inv) := by
  let idx (p : Input n inv) := n p.1
  let before (p : Input n inv) := p.2.2
  let after (p : Input n inv) := step (hs p.1) inv p.2.2 p.2.1.val
  obtain ⟨K,hK⟩ := setupCap (n := idx) (fun p => hn p.1) _ (seedSizeDom n inv)
  apply sweep n hs inv hn (fun u => t u+u)
  apply fromNative idx (fun p => hn p.1) (fun p => seed inv p.2.1.val) K hK before after (fun p => t (idx p))
  apply native.conform (fun _ => rfl) (fun _ => rfl)
  · intro p; rw [packedRows_pack,clothRows_encode]
  · intro p; rw [packedRows_scatter,clothRows_encode]

end
end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
