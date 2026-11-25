import OAI.Computability.BorderVNP.ShortenSeedDescriptorPorts

/-!
# Capacity of local bank slices for repeated interval records

A cable name identifies the record. Bit lookups use the bank addresses of
the owning cell. Restricting an existing rectangular port to any selected
interval preserves the cell's address bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing CellSparse

/-- Every copy and lane of a rectangular port lies in the given cell's local bit bank. -/
def FitsBank (capacity copies width : ℕ) (p : Port) : Prop :=
  ∀ copy < copies, ∀ lane < width, p.atBit copy lane < capacity

/-- A single upper-endpoint test suffices for a nonempty repeated, strided port. -/
theorem fitsBank_iff (capacity copies width : ℕ) (p : Port) :
    FitsBank capacity copies width p ↔ copies = 0 ∨ width = 0 ∨
      p.atBit (copies-1) (width-1) < capacity := by
  constructor
  · intro h
    by_cases hc : copies = 0
    · exact Or.inl hc
    by_cases hw : width = 0
    · exact Or.inr (Or.inl hw)
    exact Or.inr (Or.inr (h _ (by omega) _ (by omega)))
  · rintro (rfl | rfl | hend) copy hc lane hl
    · omega
    · omega
    · apply lt_of_le_of_lt _ hend
      unfold Port.atBit
      gcongr <;> omega

variable {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (m : ℕ)

/-- Both sides of the sparse concatenation row stay in their owning cell's bank whenever the
original full cable port and the common terminal-word port fit there. -/
theorem concatRow_fits (binName : A → ℕ) (positive : N.Edge → Bool) (a : A) (d : Fin D)
    (e : {e : N.Edge // bin e = some (perm d a)}) (capacity copies : ℕ) (old terminal : Port)
    (ho : FitsBank capacity copies (N.width e.val) old)
    (ht : FitsBank capacity copies (blocks N bin perm m a * m) terminal) :
    let desc := descriptor N bin perm m binName e (some (d,true))
    FitsBank capacity copies desc.span (desc.oldPort old) ∧
      FitsBank capacity copies desc.span (desc.terminalPort terminal) := by
  dsimp only
  have hw := descriptor_width N bin perm m binName e (some (d,true))
  constructor <;> intro copy hc lane hl
  · let k : Fin ((layout N bin perm m).width (e.val,some (d,true))) := ⟨lane,hl.trans_eq hw.symm⟩
    exact (oldPort_atBit N bin perm m binName e (some (d,true)) old copy k).trans_lt
      (ho copy hc _ (N.bandOrder (label N bin perm m) e.val (some (d,true)) k).val.isLt)
  · let k : Fin ((layout N bin perm m).width (e.val,some (d,true))) := ⟨lane,hl.trans_eq hw.symm⟩
    exact (terminalPort_atBit N bin perm m binName positive a d e terminal copy k).trans_lt
      (ht copy hc _ ((bundle N bin perm m positive a).order d ⟨prefixEdge N bin perm m a d e,k⟩).isLt)

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
