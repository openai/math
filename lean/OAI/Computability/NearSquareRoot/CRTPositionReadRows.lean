import OAI.Computability.NearSquareRoot.CRTPositionLayerTable

/-! # Interpreting unary position read tables on full address words

Each direction is represented by one optional unary source index per destination
bit. The row operations read only these tables and the original address word.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication.Code

/-- Decode a port whose source and destination lie in equal-width chunks. Missing
entries and out-of-range indices disable the XOR at that destination. -/
def decodePort {m : ℕ} (t : List (Option Tally)) (i : Fin m) : Option (Fin m) :=
  (Iter.pick none (t,tally i.val)).bind fun j =>
    if h : j.length < m then some ⟨j.length,h⟩ else none

@[simp] theorem decodePort_encoded {m : ℕ} (q : Fin m → Option (Fin m)) :
    decodePort (List.ofFn fun i => unaryPort (q i)) = q := by
  funext i
  unfold decodePort
  rw [Iter.entry]
  cases h : q i with
  | none => rfl
  | some j => simp [unaryPort,j.isLt]

/-- Replace the two named chunk rows of the full word, preserving each residual position. -/
def writeRows {k : ℕ} (s d : Fin 3) (rows : (Fin (k/3) → Bool) × (Fin (k/3) → Bool))
    (w : Fin k → Bool) (x : Fin k) : Bool :=
  match threeChunksWithTail k x with
  | .inr _ => w x
  | .inl (c,i) => if c=s then rows.1 i else if c=d then rows.2 i else w x

/-- Execute three XORs. The first table describes reads by the second chunk
from the first, and the second table describes the opposite direction. -/
def crossFromRows {k : ℕ} (codes : List (Option Tally) × List (Option Tally))
    (s d : Fin 3) (w : Fin k → Bool) : Fin k → Bool :=
  writeRows s d (exchangeRows (decodePort codes.2) (decodePort codes.1) (chunkWord w s,chunkWord w d)) w

/-- Execute nine XORs using the diagonal borrow, forward-partner and backward-partner ports. -/
def borrowFromRows {k : ℕ} (codes : List BorrowPorts) (c d : Fin 3) (w : Fin k → Bool) :
    Fin k → Bool :=
  let idRead := decodePort (m := k/3) (codes.map Prod.fst)
  let upRead := decodePort (m := k/3) (codes.map (Prod.fst ∘ Prod.snd))
  let downRead := decodePort (m := k/3) (codes.map (Prod.snd ∘ Prod.snd))
  let aux := exchangeRows idRead idRead
  let middle := exchangeRows downRead upRead
  writeRows c d (aux (middle (aux (chunkWord w c,chunkWord w d)))) w

theorem crossFromRows_encoded {k : ℕ} (v : Equiv.Perm (Fin k)) (s d : Fin 3) (w : Fin k → Bool) :
    crossFromRows (List.ofFn (fun i => unaryPort (chunkRead v s d i)),
      List.ofFn (fun i => unaryPort (chunkRead v d s i))) s d w = crossWord v s d w := by
  simp only [crossFromRows,decodePort_encoded]
  rfl

theorem borrowFromRows_encoded {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (c d : Fin 3) (w : Fin k → Bool) :
    let q := nativeWithin v hv c
    borrowFromRows (List.ofFn fun i => (unaryPort (borrowIdRead q i), unaryPort (borrowUpRead q i),
      unaryPort (borrowDownRead q i))) c d w = borrowWord v hv c d w := by
  simp only [borrowFromRows,List.map_ofFn,Function.comp_def,decodePort_encoded]
  rfl

/-- Decoding both concrete outputs of the table compiler yields the intended cross-chunk move. -/
theorem crossFromRows_tables {k : ℕ} (v : Equiv.Perm (Fin k)) (s d : Fin 3) (w : Fin k → Bool) :
    let m := k/3
    crossFromRows (crossDescriptor (tally m,tally (m*s.val),tally (m*d.val),positionImages v),
      crossDescriptor (tally m,tally (m*d.val),tally (m*s.val),positionImages v)) s d w = crossWord v s d w := by
  dsimp only
  rw [crossDescriptor_native,crossDescriptor_native,crossFromRows_encoded]

/-- Decoding the concrete three-port rows yields the intended within-chunk move. -/
theorem borrowFromRows_tables {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (c d : Fin 3) (w : Fin k → Bool) :
    let m := k/3
    borrowFromRows (borrowedDescriptor (tally m,tally (m*c.val),positionImages v)) c d w =
      borrowWord v hv c d w := by
  dsimp only
  rw [borrowedDescriptor_value (chunkFits k c) v hv]
  exact borrowFromRows_encoded v hv c d w

end Controlled

end NearSquareRoot
end Computability
end OAI
