import OAI.Hierarchy.DescentPrivateTreeWidths
import OAI.Hierarchy.DescentPrivateLeafHistogram

namespace OAI
/-! # A shared root-and-leaf census of the two orientations of actual reset grains -/

namespace Hierarchy.DescentPrivateTreeRoutes
open DescentRouterSlots DescentTreePrefixIntervals DescentContactTree DescentPrivateLeafHistogram
open scoped Classical BigOperators
noncomputable section
variable {I C R G F : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype G] [Fintype F]
variable {B H n : ℕ}
variable (contact : I→C) (owner : Bool→C→G⊕F)
variable (rank : F↪Fin B) (depth : Bool→F→ℕ) (room : ∀s t,depth s t≤H)
variable (book : ∀s t, LinkId owner s (.inr t) ↪ Node (depth s t))

/-- The classification test is made separately on the two physical sides.
A paid contact is absorbed at the common extra bucket. -/
def route (s : Bool) (i : I) : Arrival B H :=
  match eqn : owner s (contact i) with
  | .inl _=>none
  | .inr t=>arrived (room s t) (rank t) (book s t ⟨contact i,eqn⟩)

omit [Fintype I] [Fintype C] [Fintype G] [Fintype F] in
theorem «matches» (s : Bool) (t : F) (i : I) (e : Physical.Edge (depth s t)) :
    hits (route contact owner rank depth room book s i) (rank t) (start H e.2) (stop H e.2) ↔
      ∃ h : owner s (contact i)=.inr t,
        cut e.1.isLt (book s t ⟨contact i,h⟩)=e.2 := by
  unfold route
  split
  · rename_i g wh
    constructor
    · rintro ⟨_, bad, _⟩
      cases bad
    · rintro ⟨h, _⟩
      cases wh.symm.trans h
  · rename_i t' wh
    by_cases same : t' = t
    · subst t'
      have geo := geometry (room s t) e.1.isLt (rank t) (book s t ⟨contact i, wh⟩) e.2
      exact ⟨fun hit => ⟨wh, geo.mp hit⟩, fun ⟨_, he⟩ => geo.mpr he⟩
    · constructor
      · rintro ⟨v, row, _⟩
        exact False.elim (same (rank.injective (congrArg Prod.fst (Option.some.inj row))))
      · rintro ⟨h, _⟩
        exact False.elim (same (Sum.inr.inj (wh.symm.trans h)))

/-- A static number of physical rows may be larger than the genuine old tape. -/
def padded (id : I↪Fin n) (field : I→Arrival B H) (j : Fin n) : Arrival B H :=
  if h : ∃i,id i=j then field h.choose else none

theorem padded_at (id : I↪Fin n) (field : I→Arrival B H) (i : I) :
    padded id field (id i)=field i := by
  let h : ∃j,id j=id i:=⟨i,rfl⟩
  simp only [padded,dite_eq_left h]
  rw [id.injective h.choose_spec]

theorem padded_count (id : I↪Fin n) (field : I→Arrival B H) (b : Fin B) (lo hi : ℕ) :
    DescentOldOccurrenceRAM.count (fun j=>hits (padded id field j) b lo hi)=
        ∑i,if hits (field i) b lo hi then 1 else 0 := by
  rw [DescentOldOccurrenceRAM.count_eq_sum]
  refine (Finset.sum_subset (Finset.subset_univ (Finset.univ.map id)) ?_).symm.trans ?_
  · intro j _ outside
    have no : ¬∃i,id i=j := by
      rintro ⟨i,rfl⟩
      exact outside (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    simp [padded,no,hits]
  · rw [Finset.sum_map]
    simp only [padded_at]

omit [Fintype R] in
theorem width (D u : ℕ) (input : Bool→I→R) (site : Bool→R→G⊕F)
    (id : I↪Fin n) (s : Bool) (t : F) (e : Physical.Edge (depth s t)) :
    let N:=DescentFixedExceptionalRouter.device D contact input site owner (fun _=>u) s (.inr t) (book s t)
    N.width e=u*DescentOldOccurrenceRAM.count
      (fun j=>hits (padded id (route contact owner rank depth room book s) j) (rank t) (start H e.2) (stop H e.2)) := by
  dsimp only
  rw [DescentPrivateTreeWidths.device_width D contact input site owner (fun _=>u) s (.inr t) (book s t) (room s t) e]
  rw [padded_count,Finset.mul_sum]
  let clean (i : I) := if hits (route contact owner rank depth room book s i) (rank t) (start H e.2) (stop H e.2) then u else 0
  have calcRow (i : I) : clean i=u*(if hits (route contact owner rank depth room book s i) (rank t) (start H e.2) (stop H e.2) then 1 else 0) := by
    unfold clean;split <;> simp_all
  simp_rw [←calcRow]
  have part : (∑i : Item contact owner s (.inr t),clean i.val)=(∑i,clean i) := by
    rw [←Finset.sum_subtype (Finset.univ.filter (fun i=>owner s (contact i)=.inr t)) (by simp) clean,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases atRoot : owner s (contact i)=.inr t
    · simp [atRoot]
    · have miss : ¬hits (route contact owner rank depth room book s i) (rank t)
          (start H e.2) (stop H e.2) := by
        intro hit
        obtain ⟨present, _⟩ := («matches» contact owner rank depth room book s t i e).mp hit
        exact atRoot present
      simp only [ite_eq_right atRoot, clean, ite_eq_right miss]
  refine Eq.trans ?_ part
  refine Finset.sum_congr ?_ ?_
  · ext i
    simp only [Finset.mem_univ]
  intro i _
  have same := member (d:=e.1.val+1) e.1.isLt (room s t) (book s t (link contact owner s (.inr t) i)) e.2
  have thisRoot : hits (route contact owner rank depth room book s i.val) (rank t) (start H e.2) (stop H e.2) ↔
      cut e.1.isLt (book s t (link contact owner s (.inr t) i))=e.2 := by
    exact («matches» contact owner rank depth room book s t i.val e).trans
      ⟨fun ⟨_,h⟩=>h,fun h=>⟨i.property,h⟩⟩
  exact if_congr (same.trans thisRoot.symm) rfl rfl

end
end Hierarchy.DescentPrivateTreeRoutes

end OAI
