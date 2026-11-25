import OAI.Computability.NearSquareRoot.SynchronizedBoxPlan
import OAI.Computability.NearSquareRoot.SynchronizedBatchSlotProduct
import OAI.Computability.NearSquareRoot.SynchronizedBoxLayout
import OAI.Computability.NearSquareRoot.SynchronizedScheduleStages
import OAI.Computability.NearSquareRoot.SynchronizedStageAdjoint

/-! # Decoding the individual physical coordinates and rows of a computed box -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication.Code Matrix SynchronizedBlocks SynchronizedLayers.ScheduleProgram
  SynchronizedPadding ResidueFourier

noncomputable section

abbrev axisMod (b : List (ℕ × ℕ)) (j : Fin (b.length/4)) := fun i => BoxFin.modulus b (axis j i)
abbrev axisPad (b : List (ℕ × ℕ)) (j : Fin (b.length/4)) := fun i => BoxFin.padding b (axis j i)
abbrev expAt (b : List (ℕ × ℕ)) (j : Fin (b.length/4)) := fun i => paddedLog (axisMod b j i)

/-- The local conventions for numbering spectator fibers and the non-Walsh address bits. -/
structure BoxLayout (b : List (ℕ × ℕ)) [∀ i, NeZero (BoxFin.modulus b i)] where
  spectator : ∀ j i, Spectators (axisMod b j) (axisPad b j) i ≃
    Fin (Fintype.card (Spectators (axisMod b j) (axisPad b j) i))
  bits : ∀ j, BlockAddress (BoxAxis b) j ≃ Fin 2 × Fin (Fintype.card (BlockAddress (BoxAxis b) j)/2)

theorem active_bound (a : ℕ) [NeZero a] : a ≤ 2^paddedLog a := by
  have := paddedLog_covers a
  have := NeZero.pos a
  omega

theorem even_card {A : Type} [Fintype A] (e : A ≃ Fin 2 × Fin (Fintype.card A / 2)) :
    Even (Fintype.card A) := by
  have h := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  exact ⟨_,h.trans (Nat.two_mul _)⟩

variable {k : ℕ} {b : List (ℕ × ℕ)} [∀ i, NeZero (BoxFin.modulus b i)]
  (layout : BoxLayout b)

/-- The actual local slot, as a function of the physical block and its opcodes. -/
def boxSlot (j : Fin (b.length/4)) : SlotDescriptor → Slot (BlockAddress (BoxAxis b) j) :=
  decodeSlot (axisMod b j) (axisPad b j) (expAt b j) (layout.spectator j)
    (fun _ => active_bound _) (fun _ => (doubled_pad_lt (NeZero.pos _)).le)
    (layout.bits j) (even_card (layout.bits j))

/-- Read a generated row in the physical padded residue address order, with the
recorded direction bit controlling the adjoint of its global operation. -/
def boxRow (hd : 4 ≤ b.length) (r : Bool × Row SlotDescriptor) :
    Matrix (∀ i, BoxAxis b i) (∀ i, BoxAxis b i) ℂ :=
  let M := rowMatrix (fun j x => (boxSlot layout j x).matrix (layout.bits j)) r.2
  (if r.1 then Mᴴ else M).submatrix (regroup hd _) (regroup hd _)

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
