import OAI.Computability.BorderVNP.PackedCuts
import OAI.Computability.BorderVNP.ShortenSeedDescriptorRanks
import OAI.Computability.BorderVNP.ShortenSeedIntervalsBundles
import Mathlib.Order.Hom.Set

/-!
# Interval descriptor arithmetic for shortening

A cable record has a public name, bin, bin offset and width. A pool interval
has two cut positions in the same bin. These six words determine the retained
width and the ordinal read at either terminal using only word arithmetic.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing Packing
open scoped Classical BigOperators

/-- Six public integer fields locating a cable interval inside one direction pool. -/
structure CutDescriptor where
  /-- The old cable name. -/
  cableId : ℕ
  /-- The bin number in the public ordering. -/
  binId : ℕ
  /-- Sum of earlier cable widths in this bin. -/
  start : ℕ
  /-- Original cable width. -/
  width : ℕ
  /-- Left cut position in the bin. -/
  lo : ℕ
  /-- Right cut position in the bin. -/
  hi : ℕ

namespace CutDescriptor

/-- First retained position in the original cable. -/
def localStart (d : CutDescriptor) := cutOffset d.start d.width d.lo

/-- Number of retained bits. -/
def span (d : CutDescriptor) := overlapWidth d.start d.width d.lo d.hi

/-- First retained position in the pool interval. -/
def ordinal (d : CutDescriptor) := d.start + d.localStart - d.lo

/-- Read one bit of the original word by adding its relative offset. -/
def oldBit (d : CutDescriptor) (i : ℕ) := d.localStart + i

/-- Read the corresponding bit in the concatenation at either terminal. -/
def terminalBit (d : CutDescriptor) (i : ℕ) := d.ordinal + i

/-- Seven-word public record; the final word caches the terminal offset for direct lookup. -/
def record (d : CutDescriptor) : Fin 7 → ℕ :=
  ![d.cableId, d.binId, d.start, d.width, d.lo, d.hi, d.ordinal]

/-- Endpoint formula for an intersection of two half-open integer intervals. -/
theorem span_eq_intersection (d : CutDescriptor) : d.span =
    min (d.start + d.width) d.hi - max d.start d.lo := by
  unfold span overlapWidth cutOffset
  omega

/-- The two arithmetic lookups name the same global ordinal on every retained bit. -/
theorem sameOrdinal (d : CutDescriptor) {i : ℕ} (h : i < d.span) :
    d.lo + d.terminalBit i = d.start + d.oldBit i := by
  simp only [terminalBit, ordinal, oldBit, localStart, span, overlapWidth, cutOffset] at *
  omega

end CutDescriptor

variable {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (m : ℕ)
variable (binName : A → ℕ)

/-- Endpoints of a prefix, a pool residue, or the final tail in the sorted bin. -/
def bandCuts (count pool : ℕ) (take : Fin D → ℕ) : Band D → ℕ × ℕ
  | none => (D * pool, count)
  | some (d,true) => (d.val * pool, d.val * pool + take d)
  | some (d,false) => (d.val * pool + take d, (d.val + 1) * pool)

/-- The public arithmetic record for one labelled cable of the actual split network. -/
noncomputable def descriptor {c : A} (e : {e : N.Edge // bin e = some c}) (b : Band D) :
    CutDescriptor :=
  let n := count N bin c
  let cuts := bandCuts n (n / D) (take N bin perm m c) b
  ⟨cableName N e.val, binName c, cableOffset N bin c e.val, N.width e.val, cuts.1, cuts.2⟩

private theorem global_mem {c : A} (e : {e : N.Edge // bin e = some c}) (b : Band D)
    (k : Fin (N.width e.val)) :
    label N bin perm m e.val k = b ↔
      (descriptor N bin perm m binName e b).lo ≤ cableOffset N bin c e.val + k.val ∧
        cableOffset N bin c e.val + k.val < (descriptor N bin perm m binName e b).hi := by
  rw [label_at]
  have hr := rank_eq_offset N bin c e k
  cases b with
  | none =>
    rw [poolLabel_tail (take_le N bin perm m c), hr]
    exact (and_iff_left (hr ▸ (rank N bin c ⟨e,k⟩).isLt)).symm
  | some z =>
    rcases z with ⟨d,b⟩
    cases b
    · rw [poolLabel_residual (take_le N bin perm m c), hr]
      rfl
    · rw [poolLabel_prefix (take_le N bin perm m c), hr]
      rfl

/-- Membership in the allocated physical band is exactly the interval test on word offsets. -/
theorem label_iff_descriptor {c : A} (e : {e : N.Edge // bin e = some c}) (b : Band D)
    (k : Fin (N.width e.val)) : label N bin perm m e.val k = b ↔
      let d := descriptor N bin perm m binName e b
      d.localStart ≤ k.val ∧ k.val < cutOffset d.start d.width d.hi := by
  exact (global_mem N bin perm m binName e b k).trans (in_overlap_iff _ _ _ _ k.val k.isLt).symm

private noncomputable def offsetOrder {c : A} (e : {e : N.Edge // bin e = some c}) (b : Band D) :
    Fin (descriptor N bin perm m binName e b).span ≃o N.BandBits (label N bin perm m) e.val b := by
  let d := descriptor N bin perm m binName e b
  let last := cutOffset d.start d.width d.hi
  have hend : last ≤ N.width e.val := min_le_left _ _
  have hspan : d.span = last - d.localStart := rfl
  refine {
    toFun := fun i => ⟨⟨d.oldBit i.val, ?_⟩, ?_⟩
    invFun := fun k => ⟨k.val.val - d.localStart, ?_⟩
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · change d.localStart + i.val < _
    have hi := i.isLt
    change i.val < d.span at hi
    omega
  · apply (label_iff_descriptor N bin perm m binName e b _).mpr
    change d.localStart ≤ d.localStart + i.val ∧ d.localStart + i.val < last
    have hi := i.isLt
    change i.val < d.span at hi
    omega
  · have hk := (label_iff_descriptor N bin perm m binName e b k.val).mp k.property
    change d.localStart ≤ k.val.val ∧ k.val.val < last at hk
    change k.val.val - d.localStart < d.span
    omega
  · intro i; apply Fin.ext; exact Nat.add_sub_cancel_left _ _
  · intro k
    apply Subtype.ext
    apply Fin.ext
    exact Nat.add_sub_of_le ((label_iff_descriptor N bin perm m binName e b k.val).mp k.property).1
  · intro i j
    change d.localStart + i.val ≤ d.localStart + j.val ↔ i.val ≤ j.val
    omega

/-- The stored intersection width is the actual width of the named new cable. -/
theorem descriptor_width {c : A} (e : {e : N.Edge // bin e = some c}) (b : Band D) :
    (layout N bin perm m).width (e.val,b) = (descriptor N bin perm m binName e b).span := by
  let E := (N.bandOrder (label N bin perm m) e.val b).toEquiv.trans
    (offsetOrder N bin perm m binName e b).symm.toEquiv
  simpa only [Fintype.card_fin] using Fintype.card_congr E

/-- The allocator's increasing lookup on the old cable is exactly addition of one word offset. -/
theorem bandOrder_eq_oldBit {c : A} (e : {e : N.Edge // bin e = some c}) (b : Band D)
    (k : Fin ((layout N bin perm m).width (e.val,b))) :
    ((N.bandOrder (label N bin perm m) e.val b k).val).val =
      (descriptor N bin perm m binName e b).oldBit k.val := by
  let alt := (Fin.castOrderIso (descriptor_width N bin perm m binName e b)).trans
    (offsetOrder N bin perm m binName e b)
  exact congrArg (fun f : Fin ((layout N bin perm m).width (e.val,b)) ≃o
      N.BandBits (label N bin perm m) e.val b => (f k).val.val)
    (Subsingleton.elim (N.bandOrder (label N bin perm m) e.val b) alt)

/-- At both ends of the actual seed bundle the matching ordinal is the cached base plus the
piece-relative index. Orientation only selects the terminal. -/
theorem bundle_order_eq_terminalBit (positive : N.Edge → Bool) (a : A) (d : Fin D)
    (e : {e : N.Edge // bin e = some (perm d a)})
    (k : Fin ((layout N bin perm m).width (e.val,some (d,true)))) :
    ((bundle N bin perm m positive a).order d ⟨prefixEdge N bin perm m a d e,k⟩).val =
      (descriptor N bin perm m binName e (some (d,true))).terminalBit k.val := by
  let desc := descriptor N bin perm m binName e (some (d,true))
  have hk : k.val < desc.span := k.isLt.trans_eq (descriptor_width N bin perm m binName e _)
  rw [bundle_order_rank, rank_eq_offset, bandOrder_eq_oldBit N bin perm m binName]
  change desc.start + desc.oldBit k.val - desc.lo = desc.terminalBit k.val
  have h := desc.sameOrdinal hk
  omega

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
