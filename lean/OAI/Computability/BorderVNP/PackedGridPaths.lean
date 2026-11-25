import OAI.Computability.BorderVNP.PackedCongestion
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! # Actual simple routes on the directed generator grid

Starting with a diameter bound in a symmetric generator alphabet, delete loops from the
chosen walks. Each endpoint translates the resulting simple path for its displacement to
the common intermediate tile. The ordered two-leg walk has precisely the visit bound used
in the probabilistic congestion argument.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CayleyPaths

open SimpleGraph
open scoped Classical
variable {G J : Type} [Group G] (step : J → G)
variable (invStep : ∀ j, ∃ k, step k = (step j)⁻¹)

/-- Cayley adjacency, dropping loops while keeping all nontrivial directed neighbor steps. -/
def graph : SimpleGraph G where
  Adj x y := x ≠ y ∧ ∃ j, x * step j = y
  symm := by
    constructor
    rintro x y ⟨hne,j,rfl⟩
    obtain ⟨k,hk⟩ := invStep j
    exact ⟨hne.symm,k,by simp [hk]⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A generator word determines an actual walk no longer than the word, even when a
generator acts trivially at this quotient level. -/
theorem word_walk (w : List J) (s : G) :
    ∃ p : (graph step invStep).Walk s (s * (w.map step).prod), p.length ≤ w.length := by
  induction w generalizing s with
  | nil => exact ⟨Walk.nil.copy rfl (by simp), by simp⟩
  | cons j w ih =>
    obtain ⟨p,hp⟩ := ih (s * step j)
    have last : s * step j * (w.map step).prod = s * ((j::w).map step).prod := by simp [mul_assoc]
    by_cases he : s = s * step j
    · exact ⟨p.copy he.symm last, by simpa using hp.trans (Nat.le_succ _)⟩
    · have ha : (graph step invStep).Adj s (s * step j) := ⟨he,j,rfl⟩
      exact ⟨(Walk.cons ha p).copy rfl last, by simpa using Nat.succ_le_succ hp⟩

/-- Choose simple paths from the identity for all displacements under a word-diameter bound. -/
theorem simple_paths (h : ℕ) (short : ∀ u : G, ∃ w : List J, w.length ≤ h ∧ (w.map step).prod = u) :
    ∃ path : ∀ u : G, (graph step invStep).Path 1 u,
      ∀ u, ((path u).val).length ≤ h := by
  choose w hw hp using short
  choose p hl using fun u => word_walk step invStep (w u) 1
  let target (u : G) : 1 * ((w u).map step).prod = u := by simp [hp]
  refine ⟨fun u => ((p u).copy rfl (target u)).toPath, fun u => ?_⟩
  exact ((p u).copy rfl (target u)).length_bypass_le_length.trans
    ((Walk.length_copy ..).le.trans ((hl u).trans (hw u)))

/-- Left translation carries Cayley adjacency to adjacency with the same generator. -/
def translate (x : G) : graph step invStep →g graph step invStep where
  toFun y := x * y
  map_rel' := by
    rintro y z ⟨hne,j,he⟩
    exact ⟨fun hz => hne (mul_left_cancel hz),j,by simp [mul_assoc,he]⟩

variable (path : ∀ u : G, (graph step invStep).Path 1 u)

/-- Ordered left translate of the chosen simple displacement path. -/
def leg (x m : G) : (graph step invStep).Walk x m :=
  ((path (x⁻¹*m)).val.map (translate step invStep x)).copy (mul_one x) (mul_inv_cancel_left ..)

/-- The support of the chosen displacement path, as used by the mean congestion calculation. -/
noncomputable def sites (u : G) : Finset G := (path u).val.support.toFinset

/-- Simplicity of the translated leg identifies its ordered visit multiplicity with the
Boolean visit in the congestion bound. -/
theorem count_leg (x m g : G) :
    (leg step invStep path x m).support.count g = legVisit (sites step invStep path) x g m := by
  let p := path (x⁻¹*m)
  have hs : (leg step invStep path x m).support = p.val.support.map (fun s => x*s) := by
    simp [leg,p,translate]
  have hd := p.nodup_support.map (Equiv.mulLeft x).injective
  have hm : g ∈ p.val.support.map (fun s => x*s) ↔ x⁻¹*g ∈ p.val.support := by
    rw [List.mem_map]
    constructor
    · rintro ⟨s,hs,hg⟩
      simpa [← hg] using hs
    · exact fun h => ⟨_,h,mul_inv_cancel_left ..⟩
  rw [hs]
  unfold legVisit sites
  by_cases h : x⁻¹*g ∈ p.val.support
  · rw [ite_eq_left (List.mem_toFinset.mpr h)]
    exact List.count_eq_one_of_mem hd (hm.mpr h)
  · rw [ite_eq_right (fun hf => h (List.mem_toFinset.mp hf))]
    exact List.count_eq_zero.mpr (fun hh => h (hm.mp hh))

/-- Concatenate the first translated leg with the reverse of the second one. -/
def route (x y m : G) : (graph step invStep).Walk x y :=
  (leg step invStep path x m).append (leg step invStep path y m).reverse

/-- Counting the middle tile on both legs only enlarges the actual ordered visit count. -/
theorem count_route {W : Type*} (left right : W → G) (w : W) (m g : G) :
    (route step invStep path (left w) (right w) m).support.count g ≤
      routeVisit (sites step invStep path) left right w g m := by
  unfold route routeVisit
  rw [Walk.support_append, List.count_append, ← count_leg, ← count_leg]
  apply Nat.add_le_add_left
  rw [Walk.support_reverse, ← List.count_reverse (l := (leg step invStep path (right w) m).support)]
  exact List.Sublist.count_le g (List.tail_sublist _)

/-- The uniform translated routes with the specified endpoints can be fixed so their
actual ordered visits satisfy the simultaneous bound of Proposition 7.2. -/
theorem exists_walks [Fintype G] {W : Type*} [Fintype W] (left right : W → G) (k h : ℕ)
    (hleft : ∀ g, (Finset.univ.filter fun w => left w = g).card ≤ k)
    (hright : ∀ g, (Finset.univ.filter fun w => right w = g).card ≤ k)
    (short : ∀ u : G, ∃ w : List J, w.length ≤ h ∧ (w.map step).prod = u) :
    ∃ walk : ∀ w, (graph step invStep).Walk (left w) (right w),
      ∀ g : G, (∑ w, ((walk w).support.count g : ℝ)) ≤
        8*k*(h+1) + Real.log (Fintype.card G) := by
  obtain ⟨p,hp⟩ := simple_paths step invStep h short
  have hs (u : G) : (sites step invStep p u).card ≤ h+1 := by
    rw [sites,List.toFinset_card_of_nodup (p u).nodup_support,(p u).val.length_support]
    exact Nat.succ_le_succ (hp u)
  obtain ⟨mid,hm⟩ := exists_low_congestion_routes (sites step invStep p) left right k (h+1) hleft hright hs
  refine ⟨fun e => route step invStep p (left e) (right e) (mid e), fun g => ?_⟩
  exact (Finset.sum_le_sum fun e _ => Nat.cast_le.mpr (count_route step invStep p left right e (mid e) g)).trans
    (by simpa using hm g)

end Packing.CayleyPaths

end BorderVNP
end Computability
end OAI
