import OAI.Computability.BorderVNP.PackedBottomReportBundle
import OAI.Computability.BorderVNP.PackedBottomNamedReads
import OAI.Computability.BorderVNP.PackedGridSidecar

/-! # Resolving bottom source names against the actual ordered use stream

A compact use row has source-major, copy-minor order. The resolver reads the
typed physical bundle, returning false for an absent tag. At every live row
it returns the original selected wire in the indicated copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse DiagonalTallyCellReports
open scoped Classical

/-- The recursive name condition is the row-major address equation for each
actual sidecar ordinal. -/
theorem namedAt_iff (bank : ℕ → Bool) (use : Port → Bool) (copies copy cursor : ℕ) (ps : List (Port × ℕ)) :
    NamedAt bank use copies copy cursor ps ↔ ∀ i : Fin ps.length,
      bank (cursor+i.val*copies+copy) = use (ps.get i).1 := by
  induction ps generalizing cursor with
  | nil => simp [NamedAt]
  | cons p ps ih =>
    rcases p with ⟨tag,rel⟩
    rw [NamedAt,ih]
    constructor
    · rintro ⟨head,tail⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using head
      · simpa only [Fin.val_succ,List.get_eq_getElem,List.getElem_cons_succ,Nat.succ_mul,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail j
    · intro h
      exact ⟨by simpa using h 0,fun i => by
        simpa only [Fin.val_succ,List.get_eq_getElem,List.getElem_cons_succ,Nat.succ_mul,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h i.succ⟩

/-- Read a live tag's original rank in the immutable order; absent tags use
the Boolean zero. -/
noncomputable def resolve (tags : List Port) (read : Fin tags.length → Bool) (p : Port) : Bool :=
  if h : p ∈ tags then read ⟨tags.idxOf p,List.idxOf_lt_length_iff.mpr h⟩ else false

/-- In a directory with distinct source names the lookup recovers the exact
rank, including for a false selected wire. -/
theorem resolve_get (tags : List Port) (read : Fin tags.length → Bool) (unique : tags.Nodup)
    (i : Fin tags.length) : resolve tags read (tags.get i) = read i := by
  rw [resolve,dite_eq_left (List.get_mem tags i)]
  exact congrArg read (Fin.ext (unique.idxOf_getElem i.val i.isLt))

/-- A lookup of a named source uses the real typed bundle's selected-wire bit. -/
noncomputable def bundleUse (h : BundleHeader) (body original : List Factor) (bank : ℕ → Bool)
    (i : Fin h.copies) : Port → Bool :=
  let tags := (sidecar h.orig original).map Prod.fst
  resolve tags (fun r => (physicalBundle h body original bank).uses
    (finProdFinEquiv (⟨r.val,by simpa [tags,physicalBundle] using r.isLt⟩,i)))

/-- Reading the resolved tag at row r is exactly the physical selected-wire
choice at that row and copy. -/
theorem bundleUse_row (h : BundleHeader) (body original : List Factor) (bank : ℕ → Bool)
    (i : Fin h.copies) (unique : ((sidecar h.orig original).map Prod.fst).Nodup)
    (r : Fin (sidecar h.orig original).length) :
    bundleUse h body original bank i ((sidecar h.orig original).get r).1 =
      (physicalBundle h body original bank).uses (finProdFinEquiv (⟨r.val,by simpa [physicalBundle] using r.isLt⟩,i)) := by
  let tags := (sidecar h.orig original).map Prod.fst
  let u : Fin tags.length := ⟨r.val,by simpa [tags,physicalBundle] using r.isLt⟩
  have he : tags.get u = ((sidecar h.orig original).get r).1 := by simp [tags,u,List.get_eq_getElem]
  unfold bundleUse
  rw [← he,resolve_get _ _ unique u]

/-- Passing the actual physical box and supplemental links binds all its names
to the bits read by the native scanner. -/
theorem namedAt_physicalBundle (h : BundleHeader) (body original : List Factor) (bank : ℕ → Bool)
    (boxes : List (List Factor)) (cursor : ℕ) (i : Fin h.copies)
    (unique : ((sidecar h.orig original).map Prod.fst).Nodup)
    (hs : h.stride = bottomStride h.orig h.cap) (hc : count original ≤ h.cap)
    (reportPass : ∀ row ∈ reportRows h.boxBase h.orig h.cap h.copies cursor original, row.Valid boxes bank)
    (boxPass : ∀ f ∈ stage h.orig original, (f.observe bank (h.boxBase+i.val*h.stride) i.val).isSome = true) :
    NamedAt bank (bundleUse h body original bank i) h.copies i.val cursor (sidecar h.orig original) := by
  rw [namedAt_iff]
  intro r
  rw [bundleUse_row h body original bank i unique r]
  exact (physicalBundle_use_forced h body original bank boxes cursor ⟨r.val,by simpa using r.isLt⟩ i hs hc reportPass boxPass).symm

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
