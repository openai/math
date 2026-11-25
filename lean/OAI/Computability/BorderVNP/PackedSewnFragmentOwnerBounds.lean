import OAI.Computability.BorderVNP.PackedSewnFragmentMaximal
import OAI.Computability.BorderVNP.PackedSewnFragmentPairSpec
import OAI.Computability.BorderVNP.PackedSewnFragmentProjection
import OAI.Computability.BorderVNP.PackedSewnFragmentSort

/-! # Attained owners and exclusive address bounds of the sparse sewing stream

Every enabled raw fragment is read from its site's partial map. Sorting drops empty
fragments. A merge carries the left owner and the exclusive endpoints of its continuing
right fragment, so every emitted interval has a real site and both ends fit the word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open private coalesce_sites from OAI.Computability.BorderVNP.PackedSewnFragmentProjection

variable {V : Type*} {w n : ℕ}

/-- The enable flag identifies an actual member of the decoded chronological list. -/
theorem active_mem {x : Pin n w → Bool} {i : Fin n} (live : active x i = true) : parse x i ∈ list x := by
  apply List.mem_filterMap.mpr
  exact ⟨i,List.mem_finRange i,by simp [live]⟩

/-- A fragment in the global array occurs at its owner without changing any interval fields. -/
theorem mem_at_owner {L : List Parsed} {a : Parsed} (ha : a ∈ L) {v : ℕ} (owner : a.site=v) :
    a.run ∈ siteRuns v L := by
  apply List.mem_filterMap.mpr
  exact ⟨a,ha,by simp [owner]⟩

/-- Each merged owner was already present in the original stream. The selected witness is
an actual input occurrence; the merged interval itself may be wider than that occurrence. -/
theorem coalesce_owner {L : List Parsed} {r : Parsed} (hr : r ∈ coalesce L) :
    ∃ a ∈ L, a.site = r.site := by
  have mem := (coalesce_sites L).subset (List.mem_map.mpr ⟨r,hr,rfl⟩)
  exact List.mem_map.mp mem

/-- The two exclusive addresses used by the comparison circuit fit whenever this true
owner's old and new incidence extents fit the word. This also applies to zero-width rows. -/
theorem fits_at_owner {L : List Parsed} {a : Parsed} (ha : a ∈ L) {key old next : ℕ}
    (owner : a.site = key) {read : Fin old → Option (Fin next)}
    (cover : Covers (siteRuns key L) read) (oldRoom : old < 2^w) (newRoom : next < 2^w) : a.Fits w := by
  have mem := mem_at_owner ha owner
  exact ⟨(cover.oldFit _ mem).trans_lt oldRoom,fun j hj => (cover.newFit _ mem j hj).trans_lt newRoom⟩

variable (key : V → ℕ) (old next : V → ℕ) (read : ∀ v, Fin (old v) → Option (Fin (next v)))

/-- Pointwise fit for all enabled raw occurrences, extracted from the true per-site covers. -/
theorem raw_fits {L : List Parsed} (owned : ∀ a ∈ L, ∃ v, a.site=key v)
    (cover : ∀ v, Covers (siteRuns (key v) L) (read v))
    (oldRoom : ∀ v, old v < 2^w) (newRoom : ∀ v, next v < 2^w) :
    ∀ a ∈ L, a.Fits w := by
  intro a ha
  obtain ⟨v,hv⟩ := owned a ha
  exact fits_at_owner ha hv (cover v) (oldRoom v) (newRoom v)

/-- The actual sorter exposes a positive input witness for every coalesced owner's word,
and the exclusive ends of its merged interval fit the public word width. Only the retained
positive raw fragments need valid owner keys and bounds. -/
theorem Sorted.coalesced_owner_fits {x y : Pin n w → Bool} (h : Sorted x y)
    (owned : ∀ a ∈ list x, 0 < a.run.width → ∃ v, a.site=key v)
    (fit : ∀ a ∈ list x, 0 < a.run.width → a.Fits w) {r : Parsed} (hr : r ∈ coalesce (list y)) :
    (∃ a ∈ list x, 0<a.run.width ∧ a.site=r.site) ∧ (∃ v, r.site=key v) ∧ r.Fits w := by
  have real {a : Parsed} (ha : a ∈ list y) : a ∈ list x ∧ 0 < a.run.width := by
    obtain ⟨mem,on⟩ := List.mem_filter.mp (h.perm.subset ha)
    exact ⟨mem,of_decide_eq_true on⟩
  obtain ⟨a,ha,site⟩ := coalesce_owner hr
  have src := real ha
  obtain ⟨v,hv⟩ := owned a src.1 src.2
  exact ⟨⟨a,src.1,src.2,site⟩,⟨v,site.symm.trans hv⟩,coalesce_fits (fun p hp => fit p (real hp).1 (real hp).2) r hr⟩

/-- A sorted stream produced from complete physical covers needs no separate arithmetic
or owner assumptions on its coalesced output. -/
theorem Sorted.covered_owner_fits {x y : Pin n w → Bool} (h : Sorted x y)
    (owned : ∀ a ∈ list x, ∃ v, a.site=key v)
    (cover : ∀ v, Covers (siteRuns (key v) (list x)) (read v))
    (oldRoom : ∀ v, old v < 2^w) (newRoom : ∀ v, next v < 2^w) {r : Parsed}
    (hr : r ∈ coalesce (list y)) : (∃ v, r.site=key v) ∧ r.Fits w :=
  (h.coalesced_owner_fits key (fun a ha _ => owned a ha)
    (fun a ha _ => raw_fits key old next read owned cover oldRoom newRoom a ha) hr).2

/-- Every enabled row of the actual sort/merge frame is owned by a genuine site and
contains two valid exclusive addresses. This is the owner condition consumed by the
frozen-tape image at the sewn state. -/
theorem maximal_active_owner_fits (x : Pin n w → Bool)
    (owned : ∀ a ∈ list x, ∃ v, a.site=key v)
    (cover : ∀ v, Covers (siteRuns (key v) (list x)) (read v))
    (oldRoom : ∀ v, old v < 2^w) (newRoom : ∀ v, next v < 2^w) (i : Fin n)
    (live : active ((maximal n w).eval x) i = true) :
    let r := parse ((maximal n w).eval x) i
    (∃ v, r.site=key v) ∧ r.Fits w := by
  intro r
  have fit := raw_fits key old next read owned cover oldRoom newRoom
  have member : r ∈ list ((maximal n w).eval x) := active_mem live
  rw [maximal_list x (fun a ha _ => fit a ha)] at member
  exact (sortedFrame_values x).covered_owner_fits key old next read owned cover oldRoom newRoom member

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
