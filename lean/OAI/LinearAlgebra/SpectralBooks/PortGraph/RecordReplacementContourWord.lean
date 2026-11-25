import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementContour
import OAI.Geometry.HyperbolicGroups.BoundaryList

/-! # Boundary words of numbered patch records

The positive boundary word starts at the lexicographically first stub. A closed
patch starts at its first dart, and a patch with no darts has the empty word.
Reading the fixed darts in traversal order numbers the stubs for replacement.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

namespace PortGraph.PatchShape

variable {K : ℕ} (R : PatchShape K)

/-- The positive orbit based at a dart, including singleton orbits. -/
def contourFrom (x : R.Dart) : List R.Dart :=
  if R.contourPerm x = x then [x] else R.contourPerm.toList x

theorem contourFrom_isBoundary (x : R.Dart) : IsBoundary R.contourPerm (R.contourFrom x) := by
  unfold contourFrom
  split_ifs with hx
  · refine ⟨by simp, ?_⟩
    intro y hy
    obtain rfl := List.mem_singleton.mp hy
    simpa using hx
  · refine ⟨nodup_toList _ _, ?_⟩
    intro y hy
    rw [formPerm_toList, cycleOf_apply, ite_eq_left (mem_toList_iff.mp hy).1]

@[simp] theorem contourFrom_head (x : R.Dart) : (R.contourFrom x).head? = some x := by
  unfold contourFrom
  split_ifs with h
  · rfl
  · have hx := mem_support.mpr h
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (length_toList_pos_of_mem_support _ _ hx),
      toList_getElem_zero _ _ hx]

theorem mem_contourFrom (hc : R.InternallyConnected) (x y : R.Dart) : y ∈ R.contourFrom x :=
  (R.contourFrom_isBoundary x).mem_of_sameCycle
    (List.mem_of_mem_head? (by simp)) (R.contourPerm_sameCycle hc x y)

/-- The least stub in the recorded order of vertex and slot numbers. -/
def contourAnchor (h : Nonempty R.Stub) : R.Stub :=
  letI := R.dartOrder
  Finset.univ.min' (@Finset.univ_nonempty R.Stub _ h)

theorem contourAnchor_le (h : Nonempty R.Stub) (s : R.Stub) :
    R.dartOrder.le (R.contourAnchor h).val s.val := by
  let := R.dartOrder
  exact Finset.min'_le (Finset.univ : Finset R.Stub) s (Finset.mem_univ s)

/-- Start at the least stub, or at the least dart if every dart is paired. -/
def contourWord : List R.Dart :=
  letI := R.dartOrder
  if hs : Nonempty R.Stub then R.contourFrom (R.contourAnchor hs).val
  else if hd : Nonempty R.Dart then R.contourFrom (Finset.univ.min' (@Finset.univ_nonempty _ _ hd))
  else []

theorem contourWord_isBoundary : IsBoundary R.contourPerm R.contourWord := by
  unfold contourWord
  split_ifs
  · exact R.contourFrom_isBoundary _
  · exact R.contourFrom_isBoundary _
  · exact ⟨by simp, by simp⟩

theorem mem_contourWord (hc : R.InternallyConnected) (x : R.Dart) : x ∈ R.contourWord := by
  unfold contourWord
  split_ifs with hs hd
  · exact R.mem_contourFrom hc _ _
  · exact R.mem_contourFrom hc _ _
  · exact (hd ⟨x⟩).elim

theorem contourWord_head_of_stub (h : Nonempty R.Stub) :
    R.contourWord.head? = some (R.contourAnchor h).val := by
  simpa only [contourWord, dite_eq_left h] using R.contourFrom_head (R.contourAnchor h).val

/-- Retain exactly the stubs, in the order they occur in the boundary word. -/
def contourStubWord : List R.Stub :=
  (R.contourWord.filter fun x => decide (R.opposite x = x)).attachWith _
    (fun _ hx => of_decide_eq_true (List.mem_filter.mp hx).2)

theorem contourStubWord_values : R.contourStubWord.map Subtype.val =
    R.contourWord.filter (fun x => decide (R.opposite x = x)) := by
  simp [contourStubWord]

theorem contourStubWord_nodup : R.contourStubWord.Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [R.contourStubWord_values]
  exact R.contourWord_isBoundary.nodup.filter _

theorem mem_contourStubWord (hc : R.InternallyConnected) (s : R.Stub) : s ∈ R.contourStubWord := by
  rw [contourStubWord, List.mem_attachWith, List.mem_filter]
  exact ⟨R.mem_contourWord hc _, decide_eq_true s.property⟩

private def contourWordEquiv (hc : R.InternallyConnected) : Fin R.contourStubWord.length ≃ R.Stub :=
  List.Nodup.getEquivOfForallMemList _ R.contourStubWord_nodup (R.mem_contourStubWord hc)

theorem length_contourStubWord (hc : R.InternallyConnected) :
    R.contourStubWord.length = Fintype.card R.Stub := by
  simpa using Fintype.card_congr (R.contourWordEquiv hc)

/-- Number the stubs of a connected record in positive boundary order. -/
def contourStubEquiv (hc : R.InternallyConnected) : Fin (Fintype.card R.Stub) ≃ R.Stub :=
  (finCongr (R.length_contourStubWord hc).symm).trans (R.contourWordEquiv hc)

theorem contourStubWord_eq_ofFn (hc : R.InternallyConnected) :
    R.contourStubWord = List.ofFn (R.contourStubEquiv hc) :=
  (List.ofFn_get _).symm.trans (List.ofFn_congr (R.length_contourStubWord hc) _)

theorem contourWord_filter_eq_ofFn (hc : R.InternallyConnected) :
    R.contourWord.filter (fun x => decide (R.opposite x = x)) =
      List.ofFn (fun i => (R.contourStubEquiv hc i).val) := by
  rw [← R.contourStubWord_values, R.contourStubWord_eq_ofFn hc, List.map_ofFn]
  rfl

theorem contourStubEquiv_first (hc : R.InternallyConnected) (h : Nonempty R.Stub) :
    R.contourStubEquiv hc ⟨0, Fintype.card_pos_iff.mpr h⟩ = R.contourAnchor h := by
  obtain ⟨rest, he⟩ := List.head?_eq_some_iff.mp (R.contourWord_head_of_stub h)
  have hh := congrArg List.head? (R.contourWord_filter_eq_ofFn hc)
  simp only [he, List.filter_cons, (R.contourAnchor h).property, decide_true,
    ite_true, List.head?_cons] at hh
  change some _ = _ at hh
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simpa using Fintype.card_pos_iff.mpr h),
    List.getElem_ofFn] at hh
  exact Subtype.ext (Option.some.inj hh.symm)

/-- When the last stub is designated as the output, its predecessors are the
polygon sites, in boundary order. -/
theorem contourStubWord_eq_prefix_append_last (hc : R.InternallyConnected) {n : ℕ}
    (hcard : Fintype.card R.Stub = n + 1) :
    R.contourStubWord =
      List.ofFn (fun i : Fin n => R.contourStubEquiv hc (i.castSucc.cast hcard.symm)) ++
        [R.contourStubEquiv hc ((Fin.last n).cast hcard.symm)] := by
  rw [R.contourStubWord_eq_ofFn hc, List.ofFn_congr hcard, List.ofFn_succ', List.concat_eq_append]

/-- Removing the output stub leaves the ordered list of polygon sites. -/
theorem contourStubWord_filter_ne_last (hc : R.InternallyConnected) {n : ℕ}
    (hcard : Fintype.card R.Stub = n + 1) :
    R.contourStubWord.filter (fun s => decide (s ≠ R.contourStubEquiv hc ((Fin.last n).cast hcard.symm))) =
      List.ofFn (fun i : Fin n => R.contourStubEquiv hc (i.castSucc.cast hcard.symm)) := by
  rw [R.contourStubWord_eq_prefix_append_last hc hcard, List.filter_append]
  simp

end PortGraph.PatchShape

end

end SpectralBooks
end LinearAlgebra
end OAI
