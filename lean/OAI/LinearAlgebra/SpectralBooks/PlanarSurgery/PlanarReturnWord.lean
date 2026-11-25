import OAI.LinearAlgebra.SpectralBooks.PlanarSurgery.PlanarFirstReturn
import OAI.Geometry.HyperbolicGroups.BoundaryRotation

/-! # The boundary word of a first-return permutation

Filter the oriented contour word to its named stubs. At every surviving
letter the next surviving letter is the first marked port reached after
a positive step. Rotating the word treats its closing gap in the same way.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace PlanarSurgery
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

variable {D S : Type*} [DecidableEq D] [Fintype D]
    (p : Perm D) (j : S ↪ D) (hc : Covers p j)
    (read : D → Option S) (hr : Function.IsPartialInv j read)

include hr in
omit [DecidableEq D] [Fintype D] in
private theorem filter_nodup {w : List D} (hw : w.Nodup) : (w.filterMap read).Nodup :=
  hw.filterMap fun x y s hx hy => ((hr s x).mp hx).symm.trans ((hr s y).mp hy)

include hr in
/-- Along an arc ending at a marked dart, the scan stops at the first
surviving letter. The unscanned suffix closes the cyclic word. -/
private theorem firstStub_arc (s : S) (xs tail : List D)
    (h : IsBoundary p (xs ++ j s :: tail)) :
    firstStub p j hc (xs.headD (j s)) = (xs.filterMap read).headD s := by
  induction xs generalizing tail with
  | nil => simp
  | cons x xs ih =>
    rw [List.headD_cons]
    cases hx : read x with
    | some t =>
      obtain rfl := (hr t x).mp hx
      simp [hx]
    | none =>
      have hnot : x ∉ Set.range j := by
        rintro ⟨t,rfl⟩
        rw [hr.eq] at hx
        contradiction
      have step : p x = xs.headD (j s) := by
        cases xs with
        | nil => exact (h.turn x List.mem_cons_self).trans (List.formPerm_apply_head _ _ _ h.nodup)
        | cons y ys => exact (h.turn x List.mem_cons_self).trans (List.formPerm_apply_head _ _ _ h.nodup)
      have hturn : IsBoundary p (xs ++ j s :: (tail ++ [x])) := by
        simpa only [List.append_assoc, List.cons_append] using
          IsBoundary.rotate_append (l := [x]) (r := xs ++ j s :: tail) h
      rw [← firstStub_advance p j hc hnot, step, ih _ hturn]
      simp [hx]

variable [Fintype S] [DecidableEq S]

include hr in
omit [DecidableEq S] in
private theorem firstStub_after_head (s : S) (xs : List D) (h : IsBoundary p (j s :: xs)) :
    onStubs p j hc s = (xs.filterMap read).headD s := by
  rw [onStubs_apply]
  cases xs with
  | nil =>
    have hfix : p (j s) = j s := by simpa using h.turn (j s) List.mem_cons_self
    simp [hfix]
  | cons x xs =>
    have step := (h.turn (j s) List.mem_cons_self).trans (List.formPerm_apply_head _ _ _ h.nodup)
    rw [step]
    exact firstStub_arc p j hc read hr s (x::xs) []
      (IsBoundary.rotate_append (l := [j s]) (r := x::xs) h)

include hr in
/-- Reading just the named stubs gives a boundary of the first-return
permutation in the original orientation, including empty and singleton words. -/
theorem onStubs_boundary_of_read {w : List D} (h : IsBoundary p w) :
    IsBoundary (onStubs p j hc) (w.filterMap read) := by
  have hn := filter_nodup j read hr h.nodup
  refine ⟨hn, ?_⟩
  intro s hs
  obtain ⟨x,hx,hread⟩ := List.mem_filterMap.mp hs
  obtain rfl := (hr s x).mp hread
  obtain ⟨l,r,rfl⟩ := List.mem_iff_append.mp hx
  let tail := r ++ l
  have hb : IsBoundary p (j s :: tail) :=
    IsBoundary.rotate_append (l := l) (r := j s :: r) h
  have rot : (List.filterMap read (l ++ j s :: r)) ~r (s :: tail.filterMap read) := by
    simp only [List.filterMap_append,List.filterMap_cons,hr.eq,tail]
    exact List.isRotated_append
  rw [List.formPerm_eq_of_isRotated hn rot, firstStub_after_head p j hc read hr s tail hb]
  have hnod := rot.nodup_iff.mp hn
  cases he : tail.filterMap read with
  | nil => simp
  | cons a as =>
    rw [he] at hnod
    exact (List.formPerm_apply_head _ _ _ hnod).symm

/-- Restricting an enumerated boundary along an embedding needs only its
partial inverse to read the surviving letters. -/
theorem onStubs_boundary {w : List D} (h : IsBoundary p w) :
    IsBoundary (onStubs p j hc) (w.filterMap (Function.partialInv (j : S → D))) :=
  onStubs_boundary_of_read p j hc _ j.injective.isPartialInv h

end PlanarSurgery

end

end SpectralBooks
end LinearAlgebra
end OAI
