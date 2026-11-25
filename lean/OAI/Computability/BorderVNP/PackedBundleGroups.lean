import OAI.Computability.BorderVNP.PackedBundleSort
import Mathlib.Data.List.NodupEquivFin

/-! # Stable per-cell directory of bottom-bundle headers

The source row index identifies a retained bundle even when several bundles
have identical six-word headers. The prefix counts identify each cell's
half-open interval in the compacted directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BundleDirectory

open BottomReports

variable {N C : ℕ}

/-- Source ordinals in their original order, filtered by final cell. -/
def sourceRows (owner : Fin N → Fin C) (c : ℕ) : List (Fin N) :=
  (List.finRange N).filter fun i => decide ((owner i).val = c)

/-- Typed bundle rows in the same order as the physical stable section. -/
def groups (owner : Fin N → Fin C) (header : Fin N → BundleHeader) (c : ℕ) : List BundleHeader :=
  (sourceRows owner c).map header

/-- The start ordinal for cell `c`, measured in bundles. -/
def «prefix» (g : ℕ → List BundleHeader) : ℕ → ℕ
  | 0 => 0
  | c+1 => «prefix» g c + (g c).length

@[simp] theorem prefix_zero (g : ℕ → List BundleHeader) : «prefix» g 0 = 0 := rfl

theorem prefix_succ (g : ℕ → List BundleHeader) (c : ℕ) :
    «prefix» g (c+1) = «prefix» g c + (g c).length := rfl

theorem prefix_mono (g : ℕ → List BundleHeader) : Monotone («prefix» g) :=
  monotone_nat_of_le_succ fun c => Nat.le_add_right («prefix» g c) _

@[simp] theorem mem_sourceRows {owner : Fin N → Fin C} {c : ℕ} {j : Fin N} :
    j ∈ sourceRows owner c ↔ (owner j).val = c := by simp [sourceRows]

theorem groups_of_ge (owner : Fin N → Fin C) (header : Fin N → BundleHeader)
    {c : ℕ} (hc : C ≤ c) : groups owner header c = [] := by
  have empty : sourceRows owner c = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi =>
    ((mem_sourceRows.mp hi) ▸ (owner i).isLt).not_ge hc
  simp [groups,empty]

/-- Flattening the stable groups covers every source ordinal exactly once. -/
theorem grouped_perm (owner : Fin N → Fin C) :
    ((List.range C).flatMap (sourceRows owner)).Perm (List.finRange N) := by
  have nd : ((List.range C).flatMap (sourceRows owner)).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun c _ => (List.nodup_finRange N).filter _, List.nodup_range.imp ?_⟩
    intro c d hne
    exact List.disjoint_left.mpr fun j hc hd => hne ((mem_sourceRows.mp hc).symm.trans (mem_sourceRows.mp hd))
  apply (List.perm_ext_iff_of_nodup nd (List.nodup_finRange N)).mpr
  intro j
  simp only [List.mem_finRange, iff_true, List.mem_flatMap, List.mem_range, mem_sourceRows]
  exact ⟨(owner j).val,(owner j).isLt,rfl⟩

private theorem prefix_length (g : ℕ → List BundleHeader) (c : ℕ) :
    «prefix» g c = ((List.range c).flatMap g).length := by
  induction c with
  | zero => rfl
  | succ c ih => simp [prefix_succ, List.range_succ, ih]

/-- The past ordinal of the last group is the original number of bundles. -/
theorem prefix_groups (owner : Fin N → Fin C) (header : Fin N → BundleHeader) :
    «prefix» (groups owner header) C = N := by
  rw [prefix_length]
  change ((List.range C).flatMap fun c => (sourceRows owner c).map header).length = N
  rw [← List.map_flatMap, List.length_map, (grouped_perm owner).length_eq, List.length_finRange]

/-- Local row lookup in a cell and its inverse on source ordinals. -/
def sourceEquiv (owner : Fin N → Fin C) :
    (Σ c : Fin C, Fin (sourceRows owner c.val).length) ≃ Fin N :=
  (Equiv.sigmaCongrRight fun c =>
    ((List.nodup_finRange N).filter _).getEquiv (sourceRows owner c.val) |>.trans
      (Equiv.subtypeEquivRight fun _ => mem_sourceRows.trans Fin.ext_iff.symm)).trans
    (Equiv.sigmaFiberEquiv owner)

/-- Looking up a local ordinal in the compacted directory reads its original header. -/
theorem groups_get (owner : Fin N → Fin C) (header : Fin N → BundleHeader) (c : Fin C)
    (i : Fin (sourceRows owner c.val).length) :
    (groups owner header c.val)[i.val]'(by simp [groups]) =
      header (sourceEquiv owner ⟨c,i⟩) := List.getElem_map header

/-- Within a cell, the local ordinals strictly preserve source order. -/
theorem source_order (owner : Fin N → Fin C) (c : Fin C) :
    StrictMono (fun i => sourceEquiv owner ⟨c,i⟩) := by
  change StrictMono (sourceRows owner c.val).get
  have h : (List.finRange N).SortedLT := by
    apply StrictMono.sortedLT
    intro i j hij
    simpa using hij
  exact (List.sortedLT_iff_pairwise.mpr (h.pairwise.filter _)).strictMono_get

/-- The six-word scalar payload used by the sort is the serialization of the typed group. -/
theorem selected_fields (owner : Fin N → Fin C) (header : Fin N → BundleHeader) (c : Fin C) :
    BundleSort.selected owner header c = (groups owner header c.val).flatMap BundleHeader.words := by
  simp only [BundleSort.selected, groups, sourceRows, List.flatMap_map, Fin.ext_iff]

/-- Six scalar words per compacted bundle, including when the section is empty. -/
theorem fields_length (rows : List BundleHeader) :
    (rows.flatMap BundleHeader.words).length = 6 * rows.length := by
  induction rows with
  | nil => rfl
  | cons r rows ih => simp [BundleHeader.words, Nat.mul_succ, ih]

end Packing.BundleDirectory

end BorderVNP
end Computability
end OAI
