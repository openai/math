import OAI.ThreeFlat.Diagonal.TracePublicMemoryControls
import OAI.ThreeFlat.Diagonal.TraceUniformAddress

namespace OAI
/-! # Physical ports of the common RAM gate table -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open TraceRows TraceRowPackets
variable {w p r k S f d : ℕ}

/-- Active clock and first-clock flags for each track, zero/has-next,
and the anchor flag for each program text bit. -/
abbrev Outer (w p k : ℕ) := Fin 2 ⊕ (Fin 2 ⊕ (Bool ⊕ (Fin (1+6*p+k) × Fin w)))
abbrev Ctrl (w p k d : ℕ) := MemoryControl w d ⊕ Outer w p k
abbrev Port (w p r k d : ℕ) := TraceUniformRow.Port w p r k d ⊕ Ctrl w p k d

def outerAt (base S f : ℕ) (v : Fin (2^d)) : Outer w p k → Bool
  | .inl s => decide (S ≤ slotAddress d v s ∧ slotAddress d v s-S < f)
  | .inr (.inl s) => decide (slotAddress d v s=S ∧ 0 < f)
  | .inr (.inr (.inl false)) => decide (v.val=0)
  | .inr (.inr (.inl true)) => decide (v.val+1<2^d)
  | .inr (.inr (.inr j)) => decide ((base+(finProdFinEquiv j).val)/2=v.val)

def ctrlAt (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (base : ℕ)
    (v : Fin (2^d)) : Ctrl w p k d → Bool :=
  Sum.elim (memoryControlAt hw hs hf v) (outerAt base S f v)

def portSource (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (base : ℕ)
    (v : Fin (2^d)) : Port w p r k d → BitSource (TraceUniformRow.SharedCount w p r k d f) (S*w)
  | .inl a => TraceUniformRow.addresses (by omega) S f v a
  | .inr a => .constant (ctrlAt hw hs hf base v a)

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
