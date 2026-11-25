import OAI.Computability.BorderVNP.PackedSewnFragmentNormalize
import OAI.Computability.BorderVNP.PackedSewnFragmentSource

/-! # Site projections of the sorted exterior sewing stream

The chronological merge never crosses an owner boundary. For a stream sorted
by site, retaining one site's merged intervals gives exactly the local merge
of its input intervals, including the case of an absent owner.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

/-- The intervals belonging to one owner, in their original order. -/
def siteRuns (v : ℕ) (L : List Parsed) : List Interval :=
  L.filterMap (fun x => if x.site = v then some x.run else none)

private theorem siteRuns_cons (v : ℕ) (a : Parsed) (L : List Parsed) :
    siteRuns v (a::L) = if a.site = v then a.run :: siteRuns v L else siteRuns v L := by
  by_cases h : a.site = v <;> simp [siteRuns,h]

private theorem siteRuns_empty (v : ℕ) (L : List Parsed) (absent : ∀ a ∈ L, a.site ≠ v) :
    siteRuns v L = [] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [siteRuns_cons,ite_eq_right (absent a List.mem_cons_self)]
    exact ih fun b hb => absent b (List.mem_cons_of_mem a hb)

private theorem prepend_sites (a : Parsed) (L : List Parsed) :
    List.Sublist ((prepend a L).map Parsed.site) (a.site :: L.map Parsed.site) := by
  cases L with
  | nil => simp [prepend]
  | cons b L =>
    by_cases h : a.compatible b
    · simp only [prepend,ite_eq_left h,List.map_cons,Parsed.join]
      exact List.Sublist.cons_cons _ (List.Sublist.cons _ (List.Sublist.refl _))
    · simp [prepend,h]

private theorem coalesce_sites (L : List Parsed) :
    List.Sublist ((coalesce L).map Parsed.site) (L.map Parsed.site) := by
  induction L with
  | nil => exact List.Sublist.refl _
  | cons a L ih => exact (prepend_sites a (coalesce L)).trans (ih.cons_cons a.site)

private theorem project_prepend (v : ℕ) (a : Parsed) (L : List Parsed)
    (sorted : (a::L).Pairwise (fun x y => x.site ≤ y.site)) :
    siteRuns v (prepend a L) =
      if a.site = v then prependRun a.run (siteRuns v L) else siteRuns v L := by
  cases L with
  | nil =>
    by_cases ha : a.site = v <;> simp [siteRuns,prepend,prependRun,ha]
  | cons b L =>
    by_cases ha : a.site = v
    · by_cases hb : b.site = v
      · by_cases h : a.run.oldStart+a.run.width = b.run.oldStart ∧ a.run.source.map (·+a.run.width) = b.run.source
        · have hc : a.compatible b := ⟨ha.trans hb.symm,h⟩
          simp [prepend,hc,siteRuns_cons,Parsed.join,ha,hb,prependRun,h]
        · have hc : ¬ a.compatible b := fun hab => h hab.2
          simp [prepend,hc,siteRuns_cons,ha,hb,prependRun,h]
      · have ab : a.site ≠ b.site := fun eq => hb (eq.symm.trans ha)
        have hc : ¬ a.compatible b := fun h => ab h.1
        have lt : v < b.site := lt_of_le_of_ne (ha ▸ (List.pairwise_cons.mp sorted).1 b List.mem_cons_self) (Ne.symm hb)
        have absent : siteRuns v (b::L) = [] := by
          apply siteRuns_empty
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hb
          · exact (lt.trans_le ((List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).1 x hx)).ne'
        rw [prepend,ite_eq_right hc,siteRuns_cons,ite_eq_left ha,absent,ite_eq_left ha,prependRun]
    · by_cases hc : a.compatible b
      · have hb : b.site ≠ v := fun eq => ha (hc.1.trans eq)
        simp [prepend,hc,siteRuns_cons,Parsed.join,ha,hb]
      · simp [prepend,hc,siteRuns_cons,ha]

/-- Projecting the coalesced owner-sorted stream gives the independently
coalesced interval list of each owner. -/
theorem project_coalesce (v : ℕ) (L : List Parsed)
    (sorted : L.Pairwise (fun a b => a.site ≤ b.site)) :
    siteRuns v (coalesce L) = localRuns (siteRuns v L) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have hs : (a :: coalesce L).Pairwise (fun x y => x.site ≤ y.site) := by
      apply (List.pairwise_map (R := (· ≤ ·))).mp
      exact (List.pairwise_map.mpr sorted).sublist ((coalesce_sites L).cons_cons a.site)
    change siteRuns v (prepend a (coalesce L)) = _
    rw [project_prepend v a _ hs,ih (List.pairwise_cons.mp sorted).2,siteRuns_cons]
    by_cases ha : a.site = v <;> simp [ha,localRuns]

/-- Restricting the physical sparse merge to one site returns the exact canonical
zero and equality rows for its actual partial lane map, in increasing endpoint order. -/
theorem coalesce_intervals {old next : ℕ} (v : ℕ) (L : List Parsed) (read : Fin old → Option (Fin next))
    (sorted : L.Pairwise (fun a b => a.site ≤ b.site)) (tiles : Partition old 0 (siteRuns v L))
    (positive : ∀ p ∈ siteRuns v L, 0 < p.width) (good : ∀ p ∈ siteRuns v L, Good read p) :
    siteRuns v (coalesce L) = intervals read :=
  (project_coalesce v L sorted).trans (localRuns_eq read _ tiles positive good)

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
