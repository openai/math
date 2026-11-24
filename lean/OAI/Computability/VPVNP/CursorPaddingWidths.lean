import OAI.Computability.VPVNP.CursorPadding
import OAI.Computability.VPVNP.CursorBounds
import OAI.Computability.VPVNP.SlotDemandKernel
import OAI.Computability.VPVNP.CompressionBudget

/-!
# Bit widths and initial energy of the padded cursor network

A genuine cursor wire concatenates the message systems in their slot order.
Its zero-width copies contribute a unique empty word. Under the compressor's
equal mass per arc the initial energy therefore satisfies the bound in §12.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting RAMLayout

variable {S : Type} [Fintype S] {D p m : ℕ}

/-- Width of an actual edge, with the parallel copies carrying zero bits. -/
def paddedWidth (bits : S → ℕ) : PaddedArc D p → ℕ := Sum.elim (fun _ ↦ ∑ s, bits s) (fun _ ↦ 0)

/-- Concatenate the system fields in the supplied order. On a padded edge
the singleton symbol is equivalent to the empty bit word. -/
def paddedPayloadEquiv (order : S ≃ Fin m) (bits : S → ℕ) (e : PaddedArc D p) :
    (paddedNetwork D p bits).Payload e ≃ (Fin (paddedWidth bits e) → Bool) := by
  cases e with
  | inl _ =>
    exact (Equiv.piCurry (fun s (_ : Fin (bits s)) ↦ Bool)).symm.trans
      ((Compression.PackingData.orderedBits order bits).arrowCongr (Equiv.refl Bool))
  | inr _ => exact Equiv.ofUnique Unit (Fin 0 → Bool)

/-- The successor-mask classes precede the sorting layers, in layer ordinal order. -/
def ramSystemOrder (D : ℕ) : RAMSystem D ≃ Fin (D + layerCount D) :=
  ((Equiv.refl (Fin D)).sumCongr (layerEquiv D)).trans finSumFinEquiv

/-- The regular graph has exactly one edge for every outgoing slot at every
processor-cursor position. -/
theorem paddedEdge_card (D p : ℕ) : Fintype.card (PaddedArc D p) = (2 ^ D * D) * (2 + p) := by
  rw [Fintype.card_congr (paddedEdgeEquiv D p)]
  simp [Position, Site, Nat.mul_comm D]

/-- Upper bound on the initial square-root energy with the actual padding
and the uniform mass on the resulting edges. -/
theorem padded_sqrtEnergy_le (D p : ℕ) (bits : S → ℕ) :
    Real.sqrt (∑ e : PaddedArc D p, (paddedWidth bits e : ℝ) ^ 2 /
      (1 / (((2 ^ D * D : ℕ) : ℝ) * (2 + p : ℕ)))) ≤
      ((2 ^ D * D : ℕ) : ℝ) * (2 + p : ℕ) * (∑ s, bits s : ℕ) :=
  Compression.regularWire_sqrtEnergy_le (paddedWidth bits) (paddedEdge_card D p) (fun e ↦ by
    cases e with
    | inl _ => exact le_rfl
    | inr _ => exact Nat.zero_le _)

/-- Specialization to the RAM routing layout of §12, using its position count
and the total bit width of all successor and sorting message systems. -/
theorem cursorRAM_sqrtEnergy_le (B n p : ℕ) :
    let D := CursorBounds.virtualBits B n
    let bits : RAMSystem D → ℕ :=
      ramFieldBits (Compression.virtualBucket n) (CursorBounds.wordBits B n)
    Real.sqrt (∑ e : PaddedArc D p, (paddedWidth bits e : ℝ) ^ 2 /
      (1 / ((CursorBounds.initialPositions B n : ℝ) * (2 + p : ℕ)))) ≤
      (CursorBounds.initialPositions B n : ℝ) * (2 + p : ℕ) * (CursorBounds.initialWidth B n : ℝ) :=
  padded_sqrtEnergy_le _ p _

end CursorNetwork

end VPVNP
end Computability
end OAI
