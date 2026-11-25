import OAI.ThreeFlat.Diagonal.TraceBucketRelayValue
import OAI.ThreeFlat.Diagonal.TraceBucketJoin
import OAI.ThreeFlat.RAM.HistoryCompiledRows

namespace OAI
/-! # Mounting physical relay metadata in the complete first-layer atom -/

namespace ThreeFlat.Diagonal.TraceBucketRelay
open LaneCursor RAM RAM.BitLayout

variable {F : Type*} [CommSemiring F]

omit [CommSemiring F] in
/-- The added prefix is the first layer's genuine local external-pin array.
With zero prefix this agrees directly with HistoryCompiledRows.metadata. -/
theorem metadata_zero {p : ℕ} (tag : ((Fin 3 → Bool) → F) → ℕ) (N : BitNetwork F p)
    (c : Fin N.cells) (j : Fin 4) : metadata 0 tag N c j=RAM.HistoryCompiledRows.metadata tag N c j := by
  unfold metadata RAM.HistoryCompiledRows.metadata
  split <;> try rfl
  cases N.source c _ <;> simp [shiftedSource,sourceAddress,hiddenBase]

theorem shifted_mount {a x H : ℕ} (s : BitSource 0 a) (h : Fin 0 → Fin H) :
    sourceAddress (TraceBucketJoin.mount (Fin.natAdd x) h s) = shiftedSource x s := by
  cases s with
  | hidden j => exact Fin.elim0 j
  | constant v => rfl
  | pin j => simp [TraceBucketJoin.mount,sourceAddress,shiftedSource,Fin.val_natAdd,Nat.add_assoc]

theorem mounted_metadata {a b H x : ℕ} (A : BitNetwork F a) (ha : A.internal=0)
    (B : BitNetwork F b) (R : BitNetwork.Rectangular.Address B.internal H) (right : Fin b → Fin (x+a))
    (tag : ((Fin 3 → Bool) → F) → ℕ) (c : Fin A.cells) (j : Fin 4) :
    RAM.HistoryCompiledRows.metadata tag (TraceBucketJoin.network A ha B R (Fin.natAdd x) right)
      (c.castAdd (B.cells+H)) j = metadata x tag A c j := by
  unfold RAM.HistoryCompiledRows.metadata metadata TraceBucketJoin.network
  simp only [Fin.append_left]
  split
  case isFalse => exact congrArg tag (Fin.append_left A.table (BitNetwork.Rectangular.network B R).table c)
  cases h : A.source c _ with
  | hidden k => exact Fin.elim0 (k.cast ha)
  | constant b => rfl
  | pin q => simp [TraceBucketJoin.mount,sourceAddress,shiftedSource,Fin.val_natAdd,Nat.add_assoc]

end ThreeFlat.Diagonal.TraceBucketRelay

end OAI
