import OAI.Computability.BorderVNP.ShortenSeedDescriptor

/-!
# Uncharged cable rows

A cable outside the matching bins travels intact in its tail. All its
other reserved band rows are empty. The stable serializer therefore uses the
original width and local bit ordinal, independent of the size of the word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing Packing
open scoped Classical

variable {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (m : ℕ)

/-- Frozen cable record: the tail spans the old width and all direction pieces have width zero. -/
noncomputable def frozenDescriptor (unusedBin : ℕ) (e : N.Edge) (b : Band D) : CutDescriptor :=
  ⟨cableName N e, unusedBin, 0, N.width e, 0, if b.isNone then N.width e else 0⟩

private theorem frozen_label (e : N.Edge) (he : bin e = none) (k : Fin (N.width e)) :
    label N bin perm m e k = none := by
  unfold label
  split
  · rfl
  · rename_i c hc
    cases he.symm.trans hc

private noncomputable def frozenOrder (e : N.Edge) (he : bin e = none) :
    Fin (N.width e) ≃o N.BandBits (label N bin perm m) e none where
  toFun k := ⟨k, frozen_label N bin perm m e he k⟩
  invFun k := k.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private theorem frozen_tail (e : N.Edge) (he : bin e = none) :
    (layout N bin perm m).width (e,none) = N.width e := by
  let E := (N.bandOrder (label N bin perm m) e none).toEquiv.trans (frozenOrder N bin perm m e he).symm.toEquiv
  simpa only [Fintype.card_fin] using Fintype.card_congr E

/-- Frozen width records agree with every actual reserved row, including empty direction rows. -/
theorem frozen_width (unusedBin : ℕ) (e : N.Edge) (he : bin e = none) (b : Band D) :
    (layout N bin perm m).width (e,b) = (frozenDescriptor N unusedBin e b).span := by
  cases b with
  | none => simpa [frozenDescriptor, CutDescriptor.span, overlapWidth, cutOffset] using frozen_tail N bin perm m e he
  | some z =>
    simp only [frozenDescriptor, Option.isNone_some, Bool.false_eq_true, ite_false, CutDescriptor.span,
      overlapWidth, cutOffset, Nat.min_zero, Nat.sub_self]
    by_contra hn
    let k : Fin ((layout N bin perm m).width (e,some z)) := ⟨0,Nat.pos_of_ne_zero hn⟩
    let u := N.bandOrder (label N bin perm m) e (some z) k
    cases (frozen_label N bin perm m e he u.val).symm.trans u.property

/-- The frozen tail reads the identical ordinal of the old cable. -/
theorem frozen_oldBit (e : N.Edge) (he : bin e = none) (k : Fin ((layout N bin perm m).width (e,none))) :
    (N.bandOrder (label N bin perm m) e none k).val.val = k.val := by
  let alt := (Fin.castOrderIso (frozen_tail N bin perm m e he)).trans (frozenOrder N bin perm m e he)
  exact congrArg (fun f : Fin ((layout N bin perm m).width (e,none)) ≃o
    N.BandBits (label N bin perm m) e none => (f k).val.val)
    (Subsingleton.elim (N.bandOrder (label N bin perm m) e none) alt)

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
