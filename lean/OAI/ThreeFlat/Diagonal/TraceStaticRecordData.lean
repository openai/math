import OAI.ThreeFlat.Diagonal.TraceAddressRecord

namespace OAI
/-! # Physical records for the static trace controls

The public indices are finite sums and products. Their layout is shared with
the static trace circuit, so the native record tables can be used independently
of the circuit's evaluation proof.
-/

namespace ThreeFlat.Diagonal.TraceAddressRecord

abbrev InitIndex (w : ℕ) := Fin 2 × (Bool ⊕ (Bool × Fin (w+1)))
abbrev SortIndex (d : ℕ) := (Fin (d+2) × Fin 2) ⊕ Unit
abbrev OuterIndex (w p k : ℕ) :=
  Fin 2 ⊕ (Fin 2 ⊕ (Bool ⊕ (Fin (1+6*p+k) × Fin w)))

abbrev StaticPortIndex (w p r k d : ℕ) :=
  TraceUniformRow.Port w p r k d ⊕ ((InitIndex w ⊕ SortIndex d) ⊕ OuterIndex w p k)

variable {w p r k d : ℕ}

def interval (stride bias lo hi : ℕ) : Record :=
  { testStride := stride, testBias := bias, lo, hi, base := 1 }

def digit (stride bias sub j : ℕ) : Record :=
  { stride, base := bias, sub, bit := some j }

def initial (S f : ℕ) : InitIndex w → Record
  | (s,.inl false) => interval 2 s.val 0 S
  | (s,.inl true) => interval 2 s.val 0 (if f=0 then 0 else S+f)
  | (s,.inr (false,j)) => digit 2 s.val 0 j.val
  | (s,.inr (true,j)) => digit 2 s.val S j.val

def sort (d : ℕ) : SortIndex d → Record
  | .inl (j,s) => digit 2 s.val 0 j.val
  | .inr _ => interval 1 1 0 (2^d)

def outer (d base S f : ℕ) : OuterIndex w p k → Record
  | .inl s => interval 2 s.val S (S+f)
  | .inr (.inl s) => interval 2 s.val S (if f=0 then S else S+1)
  | .inr (.inr (.inl false)) => interval 1 0 0 1
  | .inr (.inr (.inl true)) => interval 1 1 0 (2^d)
  | .inr (.inr (.inr j)) =>
    let anchor := (base+(finProdFinEquiv j).val)/2
    interval 1 0 anchor (anchor+1)

def staticPort (hw : 3≤w+1) (base S f : ℕ) : StaticPortIndex w p r k d → Record
  | .inl a => portRecord (by omega) S f a
  | .inr (.inl (.inl a)) => initial S f a
  | .inr (.inl (.inr a)) => sort d a
  | .inr (.inr a) => outer d base S f a

end ThreeFlat.Diagonal.TraceAddressRecord

end OAI
