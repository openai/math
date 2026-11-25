import OAI.Computability.NearSquareRoot.CRTPositionChunkSwap

/-! # One physical rectangle for a chunk transposition with a spectator prefix -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication Code Strip Strip.Dims Adic Packed Loom

/-- Geometry of a three-chunk swap. The leading remainder of zero, one, or two bits is
absorbed into the prefix of the physical rectangle. -/
abbrev swapStock (k : ℕ) (op : ChunkSwap) :=
  stock 2 (field 2 (k%3 + op.front (k/3))) (field 2 (op.gap (k/3))) (field 2 (op.back (k/3))) (k/3)

def swapView (k : ℕ) (op : ChunkSwap) : Adopt (swapStock k op) (line 2 k) :=
  let n := k/3
  let hi := line 2 (k%3)
  let rest := (line 2 n).cart ((line 2 (op.gap n)).cart ((line 2 n).cart (line 2 (op.back n))))
  (((tile 2 (k%3) (op.front n)).back.split (Adopt.same rest)).thenDo
    (Adopt.rotate hi (line 2 (op.front n)) rest) |>.thenDo
    ((Adopt.same hi).split ((op.view n).thenDo (tripleView n)))).thenDo (prefixView (chunkFactor k))

theorem swapView_apply (k : ℕ) (q : Fin 3 × Fin 3)
    (a : SpanKey (field 2 (k%3+(swapOf q).front (k/3))) (field 2 ((swapOf q).gap (k/3)))
      (field 2 ((swapOf q).back (k/3))) (Block 2 (k/3))) :
    (swapView k (swapOf q)).cast (swapper _ _ _ a) = swapNative k q ((swapView k (swapOf q)).cast a) := by
  let n := k/3
  let op := swapOf q
  let ab := (tile 2 (k%3) (op.front n)).cast.symm a.1
  let low : SpanKey (field 2 (op.front n)) (field 2 (op.gap n)) (field 2 (op.back n)) (Block 2 n) := (ab.2,a.2)
  let v := prefixView (chunkFactor k)
  let t := tripleView n
  change v.cast (ab.1,t.cast ((op.view n).cast (swapper _ _ _ low))) =
    underPrefix (chunkFactor k) (tripleFlat q) (v.cast (ab.1,t.cast ((op.view n).cast low)))
  rw [underPrefix_pair,ChunkSwap.view_apply]
  simp only [tripleFlat, t, n, v, op, Equiv.symm_apply_apply]

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
