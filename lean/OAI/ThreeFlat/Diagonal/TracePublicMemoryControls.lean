import Mathlib.Tactic.Ring
import OAI.ThreeFlat.Diagonal.TraceClockSites
import OAI.ThreeFlat.Diagonal.TraceMemoryControl

namespace OAI
/-! # Public controls of the common physical memory-check circuit -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open TraceRows
variable {w S f d : ℕ}

/-- Header and CPU phase indicators, followed by bits of the address and clock at both tracks. -/
abbrev InitControl (w : ℕ) := Fin 2 × (Bool ⊕ (Bool × Fin (w+1)))

def initControlAt (S f : ℕ) (v : Fin (2^d)) : InitControl w → Bool
  | (s,.inl false) => decide (slotAddress d v s < S)
  | (s,.inl true) => decide (slotAddress d v s-S < f)
  | (s,.inr (false,j)) => (slotAddress d v s).testBit j.val
  | (s,.inr (true,j)) => (slotAddress d v s-S).testBit j.val

/-- The public slot-phase, address, clock, and sorting control wires. -/
abbrev MemoryControl (w d : ℕ) := InitControl w ⊕ TraceMemoryCircuit.MemoryControl d (w+1)

@[simp] theorem card_memoryControl (w d : ℕ) :
    Fintype.card (MemoryControl w d) = 4*(w+2)+2*(d+2)+1 := by
  simp [MemoryControl,InitControl,TraceMemoryCircuit.MemoryControl]
 ; ring

def memoryControlAt (_hw : 3 ≤ w+1) (_hs : S ≤ 2^w) (_hf : f ≤ 2^(w+1)) (v : Fin (2^d)) :
    MemoryControl w d → Bool :=
  Sum.elim (initControlAt S f v) (TraceMemoryCircuit.controlsAt v)

end ThreeFlat.Diagonal.TraceRowPackets

end OAI
