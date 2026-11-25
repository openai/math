import OAI.Computability.BorderVNP.ShortenSeedDescriptorBank
import OAI.Computability.BorderVNP.ShortenStaticRowsAccess

/-!
# Staging a cut hook separately at its two physical ends

Each incident cell ties its staging slice to the word of the physical hook.
The old end uses original-cable ordinals; the inserted end uses the common
crossing ordinals. The two records can therefore be evaluated in different
cell banks, with the hook itself carrying their shared cable word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing CellSparse

/-- Tie the appropriate staging slice to the actual cable word at one end of a physical hook. -/
def CutDescriptor.hookRow (d : CutDescriptor) (oldEnd : Bool) (copies : ℕ) (stage wire : Port) : Record :=
  .equal copies d.span (if oldEnd then d.oldPort stage else d.terminalPort stage) wire

/-- Semantic equality tested by a repeated slice-to-wire record in one cell bank. -/
def CutDescriptor.hookEq (d : CutDescriptor) (oldEnd : Bool) (copies : ℕ) (stage wire : Port)
    (bank : ℕ → Bool) : Prop :=
  ∀ copy < copies, ∀ i < d.span,
    bank ((if oldEnd then d.oldPort stage else d.terminalPort stage).atBit copy i) =
      bank (wire.atBit copy i)

variable {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (m : ℕ)
variable (binName : A → ℕ) (positive : N.Edge → Bool) (a : A) (d : Fin D)
variable (e : {e : N.Edge // bin e = some (perm d a)})

/-- At the retained site, the sparse local equality record ties exactly the original cable
positions to their corresponding lanes of the hook word. -/
theorem oldHookEq_iff (copies : ℕ) (stage wire : Port) (bank : ℕ → Bool) :
    (descriptor N bin perm m binName e (some (d,true))).hookEq true copies stage wire bank ↔
      ∀ copy < copies, ∀ k : Fin ((layout N bin perm m).width (e.val,some (d,true))),
        bank (stage.atBit copy (N.bandOrder (label N bin perm m) e.val (some (d,true)) k).val.val) =
          bank (wire.atBit copy k.val) := by
  have hw := descriptor_width N bin perm m binName e (some (d,true))
  constructor
  · intro h copy hc k
    exact (congrArg bank (oldPort_atBit N bin perm m binName e (some (d,true)) stage copy k)).symm.trans
      (h copy hc k.val (k.isLt.trans_eq hw))
  · intro h copy hc i hi
    let k : Fin ((layout N bin perm m).width (e.val,some (d,true))) := ⟨i, hi.trans_eq hw.symm⟩
    exact (congrArg bank (oldPort_atBit N bin perm m binName e (some (d,true)) stage copy k)).trans (h copy hc k)

/-- At the inserted site, the local equality record uses the exact bundle ordinals of the
same hook. The orientation flag changes which terminal's staging area is supplied. -/
theorem terminalHookEq_iff (copies : ℕ) (stage wire : Port) (bank : ℕ → Bool) :
    (descriptor N bin perm m binName e (some (d,true))).hookEq false copies stage wire bank ↔
      ∀ copy < copies, ∀ k : Fin ((layout N bin perm m).width (e.val,some (d,true))),
        bank (stage.atBit copy ((bundle N bin perm m positive a).order d ⟨prefixEdge N bin perm m a d e,k⟩).val) =
          bank (wire.atBit copy k.val) := by
  have hw := descriptor_width N bin perm m binName e (some (d,true))
  constructor
  · intro h copy hc k
    exact (congrArg bank (terminalPort_atBit N bin perm m binName positive a d e stage copy k)).symm.trans
      (h copy hc k.val (k.isLt.trans_eq hw))
  · intro h copy hc i hi
    let k : Fin ((layout N bin perm m).width (e.val,some (d,true))) := ⟨i, hi.trans_eq hw.symm⟩
    exact (congrArg bank (terminalPort_atBit N bin perm m binName positive a d e stage copy k)).trans (h copy hc k)

/-- Across all the interval records of one original cable, there is exactly one possible
staged old word for any given collection of physical band words. Empty bands need no bits. -/
theorem unique_oldStage (old : N.Edge)
    (read : ∀ b : Band D, Fin ((layout N bin perm m).width (old,b)) → Bool) :
    ∃! stage : Fin (N.width old) → Bool, ∀ b (k : Fin ((layout N bin perm m).width (old,b))),
      stage (N.bandOrder (label N bin perm m) old b k).val = read b k := by
  let E := N.bandIndex (label N bin perm m) old
  let get := fun q : Σ b : Band D, Fin ((layout N bin perm m).width (old,b)) => read q.1 q.2
  refine ⟨fun k => get (E.symm k),?_,?_⟩
  · intro b k
    exact congrArg get (E.symm_apply_apply ⟨b,k⟩)
  · intro stage hs
    funext k
    obtain ⟨⟨b,i⟩,rfl⟩ := E.surjective k
    exact (hs b i).trans (congrArg get (E.symm_apply_apply ⟨b,i⟩)).symm

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
