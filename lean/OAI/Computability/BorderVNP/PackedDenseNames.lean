import OAI.Computability.BorderVNP.PackedNames
import OAI.Computability.BorderVNP.ShortenEpochLocalRecords

/-! # Dense physical layouts behind sparse descriptor arrays

Static rectangles reserve slots for two hooks and a retained cable. A given history uses
only the slots whose cable constructors occur. Order real cables by their stable row IDs
and relabel them by their rank among those rows. This changes neither the tensor nor either
local record count. It also makes sorting by sparse row ID agree with the geometric allocator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Names

open Crossing Shortening Shortening.SeedIntervals
open scoped Classical

variable {D M : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (rows : N.Edge ↪ Fin M)

/-- Increasing rank among the occupied sparse cable slots. -/
noncomputable def denseRank : N.Edge ≃ Fin (Fintype.card N.Edge) :=
  letI := LinearOrder.lift' rows rows.injective
  (Fintype.orderIsoFinOfCardEq N.Edge rfl).symm.toEquiv

/-- Comparing dense ranks is exactly comparing the stable sparse row IDs. -/
theorem denseRank_lt (e f : N.Edge) :
    denseRank N rows e < denseRank N rows f ↔ rows e < rows f := by
  let _ := LinearOrder.lift' rows rows.injective
  exact (Fintype.orderIsoFinOfCardEq N.Edge rfl).symm.lt_iff_lt

/-- Physical presentation containing one edge per occupied descriptor row. -/
noncomputable abbrev denseLayout : Network D P bits :=
  layout N (denseRank N rows).toEmbedding (fun i => N.src ((denseRank N rows).symm i))

/-- Maps a real cable to its unique edge in the reordered physical presentation. -/
noncomputable def denseSlot : N.Edge ≃ (denseLayout N rows).Edge := slotEquiv N (denseRank N rows)

/-- The physical allocator compares cables in public sparse array order. -/
theorem denseName_lt (e f : N.Edge) :
    cableName (denseLayout N rows) (denseSlot N rows e) <
      cableName (denseLayout N rows) (denseSlot N rows f) ↔ rows e < rows f := by
  rw [denseSlot,slotEquiv_apply,slotEquiv_apply,cableName_slot,cableName_slot]
  exact denseRank_lt N rows e f

/-- Reordering the real cable records preserves the tensor on every exterior input. -/
theorem value_denseLayout {R : Type*} [CommSemiring R] (T : N.Tables R) (x : Ports bits) :
    (denseLayout N rows).value (tables N (denseRank N rows).toEmbedding
      (fun i => N.src ((denseRank N rows).symm i)) T) x = N.value T x :=
  value_layout N _ _ T x

/-- Both expanded and public local resource counts agree at every set of sites. -/
theorem localRecords_denseLayout [Fintype P] (expanded : Bool)
    (prior payload : N.Site → ℕ) (test : N.Site → Prop) :
    localRecords (denseLayout N rows) expanded prior payload test =
      localRecords N expanded prior payload test := by
  classical
  let L := denseLayout N rows
  let e := denseSlot N rows
  have edges (old : N.Edge → N.Site) (new : L.Edge → L.Site)
      (eq : ∀ i, new (e i) = old i) :
      testedWidth (fun i => recordCost expanded (L.width i)) (fun i => test (new i)) =
        testedWidth (fun i => recordCost expanded (N.width i)) (fun i => test (old i)) := by
    unfold testedWidth
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    change (if test (new (e i)) then recordCost expanded (L.width (e i)) else 0) =
      (if test (old i) then recordCost expanded (N.width i) else 0)
    rw [eq i, show L.width (e i) = N.width i from width_slot N _ _ i]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl
    (edges N.src L.src (fun i => src_slot N _ _ i)))
    (edges N.dst L.dst (fun i => dst_slot N _ _ i))) rfl

/-- The ordinal at the first bit of a live cable is the sum of preceding equal-bin
widths in the sparse array. Empty reserved rows contribute zero. -/
theorem denseOffset {A : Type} (bin : N.Edge → Option A) (a : A) (e : N.Edge) :
    cableOffset (denseLayout N rows) (bin ∘ (denseSlot N rows).symm) a (denseSlot N rows e) =
      ∑ f, if bin f = some a ∧ rows f < rows e then N.width f else 0 := by
  classical
  rw [cableOffset_eq_sum, ← (denseSlot N rows).sum_comp]
  apply Finset.sum_congr rfl
  intro f _
  change (if bin ((denseSlot N rows).symm (denseSlot N rows f)) = some a ∧
      cableName (denseLayout N rows) (denseSlot N rows f) <
        cableName (denseLayout N rows) (denseSlot N rows e)
    then (denseLayout N rows).width (denseSlot N rows f) else 0) = _
  rw [Equiv.symm_apply_apply]
  by_cases h : bin f = some a ∧ rows f < rows e
  · have hh := And.intro h.1 ((denseName_lt N rows f e).mpr h.2)
    rw [ite_eq_left h, ite_eq_left hh]
    exact width_slot N _ _ f
  · have hh : ¬(bin f = some a ∧ cableName (denseLayout N rows) (denseSlot N rows f) <
        cableName (denseLayout N rows) (denseSlot N rows e)) :=
      fun t => h ⟨t.1,(denseName_lt N rows f e).mp t.2⟩
    rw [ite_eq_right h,ite_eq_right hh]

end Packing.Names

end BorderVNP
end Computability
end OAI
