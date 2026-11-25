import OAI.Computability.BorderVNP.CellSparse
import OAI.Computability.BorderVNP.ShortenSeedDescriptor

/-!
# Wiring the compressed interval descriptors into sparse cells

A slice advances only the lane base of the original port. The copy and lane
strides may be arbitrary. Every matched interval is represented by a single
repeated equality record between its old-cable and crossing-terminal slices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing CellSparse

namespace CutDescriptor

/-- Advance a port by an offset in lanes; its two strides are preserved. -/
def slice (p : Port) (offset : ℕ) : Port :=
  ⟨p.base + offset * p.laneStride, p.copyStride, p.laneStride⟩

/-- Looking up a lane in a shifted port adds the offset to its original lane index. -/
theorem slice_atBit (p : Port) (offset copy lane : ℕ) :
    (slice p offset).atBit copy lane = p.atBit copy (offset + lane) := by
  unfold slice Port.atBit
  ring

/-- The slice on the old cable, in original bit order. -/
def oldPort (d : CutDescriptor) (p : Port) := slice p d.localStart

/-- The slice on the crossing terminal, in common matched-prefix order. -/
def terminalPort (d : CutDescriptor) (p : Port) := slice p d.ordinal

/-- One sparse concatenation record for all retained lanes across all copies. -/
def concatRow (d : CutDescriptor) (copies : ℕ) (old terminal : Port) : Record :=
  .equal copies d.span (d.oldPort old) (d.terminalPort terminal)

end CutDescriptor

variable {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (m : ℕ)
variable (binName : A → ℕ)

/-- The source address of the sparse equality is the old allocation's physical bit address. -/
theorem oldPort_atBit {c : A} (e : {e : N.Edge // bin e = some c}) (b : Band D)
    (old : Port) (copy : ℕ) (k : Fin ((layout N bin perm m).width (e.val,b))) :
    ((descriptor N bin perm m binName e b).oldPort old).atBit copy k.val =
      old.atBit copy (N.bandOrder (label N bin perm m) e.val b k).val.val := by
  rw [bandOrder_eq_oldBit N bin perm m binName]
  exact CutDescriptor.slice_atBit old _ _ _

/-- The destination address is the bundle's original, public matched ordinal in every copy. -/
theorem terminalPort_atBit (positive : N.Edge → Bool) (a : A) (d : Fin D)
    (e : {e : N.Edge // bin e = some (perm d a)}) (terminal : Port) (copy : ℕ)
    (k : Fin ((layout N bin perm m).width (e.val,some (d,true)))) :
    ((descriptor N bin perm m binName e (some (d,true))).terminalPort terminal).atBit copy k.val =
      terminal.atBit copy ((bundle N bin perm m positive a).order d ⟨prefixEdge N bin perm m a d e,k⟩).val := by
  rw [bundle_order_eq_terminalBit N bin perm m binName]
  exact CutDescriptor.slice_atBit terminal _ _ _

/-- Equality of the sparse slices checks exactly the original cable-to-terminal concatenation
at both endpoint orientations, including empty intervals and zero copies. -/
theorem concatRow_iff (positive : N.Edge → Bool) (a : A) (d : Fin D)
    (e : {e : N.Edge // bin e = some (perm d a)}) (old terminal : Port) (copies : ℕ)
    (bank : ℕ → Bool) :
    let desc := descriptor N bin perm m binName e (some (d,true))
    (∀ copy < copies, ∀ i < desc.span,
      bank ((desc.oldPort old).atBit copy i) = bank ((desc.terminalPort terminal).atBit copy i)) ↔
      ∀ copy < copies, ∀ k : Fin ((layout N bin perm m).width (e.val,some (d,true))),
        bank (old.atBit copy (N.bandOrder (label N bin perm m) e.val (some (d,true)) k).val.val) =
          bank (terminal.atBit copy
            ((bundle N bin perm m positive a).order d ⟨prefixEdge N bin perm m a d e,k⟩).val) := by
  dsimp only
  let hw := descriptor_width N bin perm m binName e (some (d,true))
  constructor
  · intro h copy hc k
    rw [← oldPort_atBit N bin perm m binName e (some (d,true)),
      ← terminalPort_atBit N bin perm m binName positive a d e]
    exact h copy hc k.val (k.isLt.trans_eq hw)
  · intro h copy hc i hi
    let k : Fin ((layout N bin perm m).width (e.val,some (d,true))) := ⟨i, hi.trans_eq hw.symm⟩
    exact (congrArg bank (oldPort_atBit N bin perm m binName e (some (d,true)) old copy k)).trans
      ((h copy hc k).trans (congrArg bank (terminalPort_atBit N bin perm m binName positive a d e terminal copy k)).symm)

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
