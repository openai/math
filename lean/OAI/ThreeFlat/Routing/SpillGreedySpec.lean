import Mathlib.Data.Bool.Basic
import OAI.ThreeFlat.Routing.SpillPrimaryMask
import OAI.ThreeFlat.Routing.SpillGreedy
import OAI.ThreeFlat.SpillSorted

namespace OAI
/-! # Agreement of checked primary links with the ordered greedy pass -/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.Spill
open Concentrator

variable {L R : Type*} [Fintype L] [LinearOrder L] [Fintype R] [LinearOrder R]

/-- Forget the neighborhood proof attached to the selected primary port. -/
def primaryReport (N : L → Finset R) (x : L → Bool) (h : Candidate N → Bool) (i : L) :
    Option R := (winner N x h i).map Subtype.val

omit [Fintype R] in
private theorem primaryReport_eq_some {N : L → Finset R} {x : L → Bool}
    {h : Candidate N → Bool} {i : L} (r : N i) :
    primaryReport N x h i = some r.val ↔ winner N x h i = some r := by
  unfold primaryReport
  cases winner N x h i with
  | none => simp
  | some a =>
    change some a.val = some r.val ↔ some a = some r
    exact ⟨fun h => congrArg some (Subtype.ext (Option.some.inj h)),
      fun h => congrArg (fun b : N i => some b.val) (Option.some.inj h)⟩

omit [Fintype R] in
theorem primaryReport_bits {N : L → Finset R} {x : L → Bool} {h : Candidate N → Bool}
    (valid : PrimaryValid N x h) (i : L) (r : N i) :
    h ⟨i,r⟩ = decide (primaryReport N x h i = some r.val) := by
  rw [valid i r]
  exact (Bool.decide_congr (primaryReport_eq_some r)).symm

private theorem reportedFree_iff {N : L → Finset R} {A : Finset L}
    {h : Candidate N → Bool} {f : L → Option R}
    (bits : ∀ i (r : N i), h ⟨i,r⟩ = decide (f i = some r.val))
    (inactive : ∀ i ∉ A, f i = none) {prior later : List L} {i : L}
    (order : A.sort = prior ++ i :: later) (r : N i) :
    r ∈ available N h i ↔
      r.val ∈ Greedy.reportedFree (fun j => (N j).sort) f prior Finset.univ := by
  simp only [available,Finset.mem_filter,Finset.mem_attach,true_and,Greedy.reportedFree,
    Finset.mem_univ,List.all_eq_true,decide_eq_true_eq,Finset.mem_sort]
  constructor
  · intro ha j hj hn
    have hb := ha (⟨j,hn⟩ : Contenders N r.val) ((Greedy.mem_sort_prefix_iff order).mp hj).2
    simpa [bits] using hb
  · intro hf j hj
    rw [bits]
    by_cases hjA : j.val ∈ A
    · simpa using hf j.val ((Greedy.mem_sort_prefix_iff order).mpr ⟨hjA,hj⟩) j.property
    · simp [inactive j.val hjA]

private theorem report_at_prefix {N : L → Finset R} {A : Finset L} {x : L → Bool}
    (mask : ∀ i, x i = true ↔ i ∈ A) {h : Candidate N → Bool} {f : L → Option R}
    (bits : ∀ i (r : N i), h ⟨i,r⟩ = decide (f i = some r.val))
    (inactive : ∀ i ∉ A, f i = none) {prior later : List L} {i : L}
    (order : A.sort = prior ++ i :: later) :
    primaryReport N x h i = Greedy.firstFree (N i).sort
      (Greedy.reportedFree (fun j => (N j).sort) f prior Finset.univ) := by
  have hi : x i = true := (mask i).mpr ((Finset.mem_sort (· ≤ ·)).mp (by simp [order]))
  have can := reportedFree_iff bits inactive order
  by_cases hn : (available N h i).Nonempty
  · let r := (available N h i).min' hn
    have hr := (available N h i).min'_mem hn
    simp only [primaryReport,winner,hi,ite_true,dite_eq_left hn,Option.map_some]
    exact (Greedy.firstFree_sort_eq_some r.val r.property ((can r).mp hr) (by
      intro q hq hfree
      exact (available N h i).min'_le ⟨q,hq⟩ ((can ⟨q,hq⟩).mpr hfree))).symm
  · simp only [primaryReport,winner,hi,ite_true,dite_eq_right hn,Option.map_none]
    apply Eq.symm
    apply List.find?_eq_none.mpr
    intro q hq hf
    let r : N i := ⟨q,(Finset.mem_sort (· ≤ ·)).mp hq⟩
    exact hn ⟨r,(can r).mpr (of_decide_eq_true hf)⟩

theorem primaryReport_padded {N : L → Finset R} {x : L → Bool} {A : Finset L}
    (mask : ∀ i, x i = true ↔ i ∈ A) {h : Candidate N → Bool} (valid : PrimaryValid N x h) :
    Greedy.PaddedLocalValid (fun i => (N i).sort) (primaryReport N x h) A.sort Finset.univ := by
  have inactive (i : L) (hi : i ∉ A) : primaryReport N x h i = none := by
    have hx : x i = false := Bool.eq_false_iff.mpr (mt (mask i).mp hi)
    simp [primaryReport,winner,hx]
  refine ⟨fun _ _ _ order => report_at_prefix mask (primaryReport_bits valid) inactive order,?_⟩
  simpa using inactive

/-- Accepted primary bits are exactly the edges of a padded valid local report. -/
theorem primaryValid_iff_padded {N : L → Finset R} {x : L → Bool} {A : Finset L}
    (mask : ∀ i, x i = true ↔ i ∈ A) (h : Candidate N → Bool) :
    PrimaryValid N x h ↔ ∃ f : L → Option R,
      Greedy.PaddedLocalValid (fun i => (N i).sort) f A.sort Finset.univ ∧
      ∀ i (r : N i), h ⟨i,r⟩ = decide (f i = some r.val) := by
  constructor
  · intro valid
    exact ⟨_,primaryReport_padded mask valid,primaryReport_bits valid⟩
  · rintro ⟨f,hf,bits⟩ i r
    have inactive : ∀ i ∉ A, f i = none := by simpa using hf.2
    have eqf : f i = primaryReport N x h i := by
      by_cases hi : i ∈ A
      · obtain ⟨prior,later,order⟩ := List.append_of_mem ((Finset.mem_sort (· ≤ ·)).mpr hi)
        exact (hf.1 prior i later order).trans (report_at_prefix mask bits inactive order).symm
      · have hx : x i = false := Bool.eq_false_iff.mpr (mt (mask i).mp hi)
        simp [inactive i hi,primaryReport,winner,hx]
    rw [bits,eqf]
    exact Bool.decide_congr (primaryReport_eq_some r)

/-- A candidate link carries a primary bit precisely when the ordered pass matched it. -/
theorem matched_iff_primary {N : L → Finset R} {x : L → Bool} {A : Finset L}
    (mask : ∀ i, x i = true ↔ i ∈ A) {h : Candidate N → Bool} (valid : PrimaryValid N x h)
    (i : L) (r : N i) :
    (i,r.val) ∈ (Greedy.run (fun j => (N j).sort) A.sort Finset.univ).matched ↔ h ⟨i,r⟩ = true := by
  have padded := primaryReport_padded mask valid
  have ok := (Greedy.localValid_iff_valid ..).mp padded.1
  rw [(Greedy.valid_iff_result ok i).1,primaryReport_bits valid i r,decide_eq_true_eq]
  refine ⟨And.right,fun hp => ⟨?_,hp⟩⟩
  by_contra inactive
  rw [padded.2 i inactive] at hp
  contradiction

theorem missedPrimary_eq_run {N : L → Finset R} {x : L → Bool} {A : Finset L}
    (mask : ∀ i, x i = true ↔ i ∈ A) {h : Candidate N → Bool} (valid : PrimaryValid N x h) :
    missedPrimary A N h = (Greedy.run (fun i => (N i).sort) A.sort Finset.univ).missed := by
  have ok := (Greedy.localValid_iff_valid ..).mp (primaryReport_padded mask valid).1
  ext i
  rw [(Greedy.valid_iff_result ok i).2]
  simp only [missedPrimary,Finset.mem_filter,Finset.mem_sort]
  apply and_congr_right
  intro _
  cases hw : winner N x h i with
  | none =>
    constructor
    · intro _
      simp [primaryReport,hw]
    · intro _ r
      simp [valid i r,hw]
  | some r =>
    have pick : h ⟨i,r⟩ = true := by simp [valid i r,hw]
    simp only [primaryReport,hw,Option.map_some,Option.some_ne_none,iff_false]
    exact fun h0 => Bool.noConfusion ((h0 r).symm.trans pick)

omit [Fintype R] in
/-- No two selected primary edges have the same destination. -/
theorem selected_primary_injective {N : L → Finset R} {x : L → Bool}
    {h : Candidate N → Bool} (valid : PrimaryValid N x h) :
    Function.Injective (fun e : {e : Candidate N // h e = true} => e.val.2.val) := by
  have before {i j : L} (r : N i) (s : N j) (heq : r.val = s.val) (lt : i < j)
      (hi : h ⟨i,r⟩ = true) (hj : h ⟨j,s⟩ = true) : False := by
    have hw := of_decide_eq_true ((valid j s).symm.trans hj)
    have avail : s ∈ available N h j := by
      unfold winner at hw
      split at hw
      · split at hw
        next hn =>
          exact (Option.some.inj hw) ▸ (available N h j).min'_mem hn
        next => contradiction
      · contradiction
    have occ := (Finset.mem_filter.mp avail).2 (⟨i,heq ▸ r.property⟩ : Contenders N s.val) lt
    rcases r with ⟨r,hr⟩
    rcases s with ⟨s,hs⟩
    dsimp at heq
    subst s
    exact Bool.noConfusion (occ.symm.trans hi)
  rintro ⟨⟨i,r⟩,hi⟩ ⟨⟨j,s⟩,hj⟩ eqn
  change r.val = s.val at eqn
  obtain lt | rfl | lt := lt_trichotomy i j
  · exact (before r s eqn lt hi hj).elim
  · have he : r = s := Subtype.ext eqn
    subst s
    rfl
  · exact (before s r eqn.symm lt hj hi).elim

end ThreeFlat.Routing.Spill

end
end OAI
