import OAI.Hierarchy.DescentTerminalGrainStreams

namespace OAI
/-! # One calendar entry per upper-triangular neighbor in the native host roster -/
namespace Hierarchy.DescentTerminalGrainProfiles
open Computability.BorderVNP.Crossing DescentTerminalCableOrder DescentTerminalSparseHeader
open scoped Classical
noncomputable section

variable {H D : ℕ} (near : Fin H→Finset (Fin H))

def tickets (i : Fin H) := ((near i).filter (i≤·)).sort.map (fun j=>pair i j)
def calendar := (Finset.univ : Finset (Fin H)).sort.flatMap (tickets near)

theorem mem_tickets {i : Fin H} {key : ℕ} :
    key∈tickets near i ↔ ∃j∈near i,i≤j ∧ pair i j=key := by
  simp [tickets,and_assoc]

theorem mem_calendar {key : ℕ} :
    key∈calendar near ↔ ∃i j : Fin H,j∈near i ∧ i≤j ∧ pair i j=key := by
  simp [calendar,mem_tickets]

private theorem pair_eq_of_le {i j : Fin H} (h : i ≤ j) :
    pair i j = i.val * H + j.val := by
  have hij : i.val ≤ j.val := h
  simp only [pair, min_eq_left hij, max_eq_right hij]

theorem calendar_sorted : (calendar near).Pairwise (·<·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    apply List.pairwise_map.mpr
    apply (((near i).filter (i≤·)).sortedLT_sort.pairwise).imp_of_mem
    intro a b ha hb ab
    have lower {x : Fin H} (hx : x ∈ ((near i).filter (i≤·)).sort) : i ≤ x := by
      have both : x ∈ near i ∧ i ≤ x := by simpa only [Finset.mem_sort,Finset.mem_filter] using hx
      exact both.2
    rw [pair_eq_of_le (lower ha),pair_eq_of_le (lower hb)]
    exact Nat.add_lt_add_left ab _
  · apply (Finset.univ.sortedLT_sort.pairwise).imp
    intro i j ij a ha b hb
    obtain ⟨x,_,ix,rfl⟩:=(mem_tickets near).1 ha
    obtain ⟨y,_,jy,rfl⟩:=(mem_tickets near).1 hb
    rw [pair_eq_of_le ix,pair_eq_of_le jy]
    exact (digit_lt x.isLt y.isLt).2 (Or.inl ij)

theorem calendar_price (small:∀i,(near i).card≤D) : (calendar near).length≤H*D := by
  have each (i:Fin H) : (tickets near i).length≤D := by
    simp only [tickets,List.length_map,Finset.length_sort]
    exact (Finset.card_le_card (Finset.filter_subset ..)).trans (small i)
  have sum (l:List (Fin H)) : (l.flatMap (tickets near)).length≤l.length*D := by
    induction l with
    | nil=>simp
    | cons a l ih=>simpa only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add (each a) ih
  let sites := (Finset.univ : Finset (Fin H)).sort
  have count : sites.length = H := by
    calc
      sites.length = (Finset.univ : Finset (Fin H)).card :=
        Finset.length_sort (s := Finset.univ) (· ≤ ·)
      _ = H := by simp
  exact (sum sites).trans (Nat.mul_le_mul_right D count.le)

variable {d : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network d P bits) (home : N.Site→Fin H)

omit [Fintype P] in
/-- Admissible pairs come only from the public neighbor roster; zero active mass pads a scheduled pair. -/
theorem calendar_catalog (covers:∀e,0<N.width e→
    home (N.dst e)∈near (home (N.src e)) ∧ home (N.src e)∈near (home (N.dst e))) :
    (calendar near).filter (fun t=>decide (0<pairMass N home t))=(occupied N home (H*H)).sort := by
  let l:=(calendar near).filter (fun t=>decide (0<pairMass N home t))
  have spec : l.toFinset=occupied N home (H*H) := by
    ext t
    unfold occupied
    rw [Finset.mem_filter]
    simp only [l,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,positive_iff,
      Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨h,existent⟩
      obtain ⟨i,j,_,ij,eqn⟩:=(mem_calendar near).1 h
      refine ⟨existent,?_⟩
      rw [←eqn,pair_eq_of_le ij]
      have step:=Nat.mul_le_mul_right H (show i.val+1≤H from i.isLt)
      rw [Nat.succ_mul] at step
      have := j.isLt
      omega
    · rintro ⟨⟨e,he,te⟩,_⟩
      refine ⟨(mem_calendar near).2 ?_,⟨e,he,te⟩⟩
      rcases le_total (home (N.src e)) (home (N.dst e)) with h|h
      · exact ⟨_,_,(covers e he).1,h,te⟩
      · exact ⟨_,_,(covers e he).2,h,(pair_swap ..).trans te⟩
  have ranked:= (calendar_sorted near).filter (fun t=>decide (0<pairMass N home t))
  rw [←spec]
  exact ((List.toFinset_sort (·≤·) (ranked.imp (fun ab=>ne_of_lt ab))).mpr (ranked.imp (fun ab=>le_of_lt ab))).symm

end
end Hierarchy.DescentTerminalGrainProfiles

end OAI
