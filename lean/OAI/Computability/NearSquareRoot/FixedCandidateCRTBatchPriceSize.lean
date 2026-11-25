import OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchPriceGrouped
import OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchPriceTable

/-! # Width bounds for the serialized bit arrays of a CRT batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTKernel
open IntegerMultiplication Code Adic Strip Loom
open Controlled

/-- The bound includes the delimiter of every payload row, including empty rows. -/
theorem cloth_count {X : Type} (k : X → ℕ) {U : X → Type}
    (u : (x : X) → Series (U x)) (f : (x : X) → Block 2 (k x) → U x → Bead) (x : X) :
    (cloth (fun x => line 2 (k x)) u f x).count ≤ 3 * 2^(k x) * ((u x).count+1) :=
  PositionProgram.position_row_count (k x) (u x) (f x)

/-- For positive-width payloads the delimiters fit in five times the data volume. -/
theorem cloth_count_le_volume {X : Type} (k : X → ℕ) {U : X → Type}
    (u : (x : X) → Series (U x)) (pos : ∀ x, 0 < (u x).count)
    (f : (x : X) → Block 2 (k x) → U x → Bead) (x : X) :
    (cloth (fun x => line 2 (k x)) u f x).count ≤ 5*(2^(k x)*(u x).count) :=
  ReserveSmall.beadClothCap k (fun x => (u x).count) u f pos (fun _ => le_rfl) x

theorem cloth_count_le_width {X : Type} (k w : X → ℕ) {U : X → Type}
    (u : (x : X) → Series (U x)) (pos : ∀ x, 0 < (u x).count) (C : ℕ)
    (vol : ∀ x, 2^(k x)*(u x).count ≤ C*(w x+1))
    (f : (x : X) → Block 2 (k x) → U x → Bead) (x : X) :
    (cloth (fun x => line 2 (k x)) u f x).count ≤ (5*C)*(w x+1) :=
  (cloth_count_le_volume k u pos f x).trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 5 (vol x))

/-- The same constants bound the initial and scattered arrays, independently of the stored bits. -/
theorem batchArrayCaps {X : Type} (p : X → Batch) {U : X → Type} (u : (x : X) → Series (U x))
    (pos : ∀ x, 0 < (u x).count) (f : (x : X) → (p x).Address → U x → Bead) (x : X) :
    (array p u f x).count ≤ 5*volume p u x ∧ (result p u f x).count ≤ 5*volume p u x := by
  constructor <;> apply cloth_count_le_volume (fun x => (p x).k) u pos

/-- One affine outer-width envelope covers all native position payloads, including
the two placement tables and the original seed. -/
theorem batchPacketCap {X : Type} (p : X → Batch) {U : X → Type} (u : (x : X) → Series (U x))
    (seedBound : Dom (fun x => (p x).k) (fun x => size (p x).seed))
    (w : X → ℕ) (occupied : ∀ x, 0 < (u x).count)
    (vol : ∃ C : ℕ, ∀ x, volume p u x ≤ C*(w x+1)) :
    ∃ C : ℕ, ∀ x (π : Equiv.Perm (Fin (p x).k))
      (data : Block 2 (p x).k → U x → Bead),
      size (p x).seed + size (Reflections.table π) + size (Reflections.table π.symm) +
        (stripe (line 2 (p x).k) (fun a => strip (u x) (data a))).count + 3 ≤ C*(w x+1) := by
  obtain ⟨B,seed⟩ := seed_tables_le_width p seedBound occupied vol
  obtain ⟨L,hL⟩ := vol
  refine ⟨B+5*L+3,fun x π data => ?_⟩
  have tab := seed x π
  have h := occupied x
  have row : (stripe (line 2 (p x).k) (fun a => strip (u x) (data a))).count ≤
      5*volume p u x := by
    exact ReserveSmall.beadClothCap (I := Unit) (fun _ => (p x).k)
      (fun _ => (u x).count) (fun _ => u x) (fun _ => data) (fun _ => h) (fun _ => le_rfl) ()
  have hv := row.trans (Nat.mul_le_mul_left 5 (hL x))
  rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc]
  omega

end FixedCandidate.CRTKernel

end NearSquareRoot
end Computability
end OAI
