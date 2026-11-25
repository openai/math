import OAI.ThreeFlat.RAM.TickIntervalRows

namespace OAI
/-! # The endpoint relation at one physical chunk -/

namespace ThreeFlat.RAM.TickChunkCheck

open TickIntervalCursor Diagonal.TickGroupIntervals

def chunkSize (L : Layout) := L.chunkEnd-L.chunkStart

def codeAt (L : Layout) (es : List Interval) (i : ℕ) := pairCode L.group (L.chunkStart+i) es

/-- The field-independent endpoint predicate checked by the two generated
records for every bit. -/
def valid (groupScan : Bool) (L : Layout) (es : List Interval) (op np : ℕ → Bool)
    (a b : Fin (chunkSize L) → Bool) : Prop :=
  ∀ i, if groupScan = true ∧ codeAt L es i.val ≠ 0 then
    a i = op (codeAt L es i.val-1) ∧ b i = np (codeAt L es i.val-1) else a i = b i

theorem valid_preserve (L : Layout) (es : List Interval) (op np : ℕ → Bool)
    (a b : Fin (chunkSize L) → Bool) : valid false L es op np a b ↔ a = b := by
  simp [valid,funext_iff]

end ThreeFlat.RAM.TickChunkCheck

end OAI
