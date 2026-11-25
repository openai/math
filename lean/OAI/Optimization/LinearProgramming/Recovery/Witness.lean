import OAI.Optimization.LinearProgramming.Farkas.Subspace
import OAI.Optimization.LinearProgramming.Geometry.MinimalSupport
import OAI.Optimization.LinearProgramming.Recovery.Restart

/-! Section 2.3. Decision-to-witness reduction over any ordered field. The inputs to the
subspace oracle are representations `R`. The caller implements complement and coordinate
restriction on these representations (the paper uses elimination on original equations).
The reduction orients the line generator itself and records its actual oracle arguments. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

variable {K : Type*}

open Geometry

variable {K R : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- The two sides share one marked coordinate; the returned point is scaled to one there. -/
structure WitnessResult (K R : Type*) (n : ℕ) where
  primal : Bool
  allowed : Finset (Fin n)
  point : Fin n → K
  queries : List R

/-- The outer `decide` call selects the side. Each further query erases just one index
from the currently allowed support. An arbitrary nonzero row of the final line suffices. -/
def recoverWitness (decide : R → Bool) (complement : R → R)
    (restrict : R → Finset (Fin n) → R) (generator : R → Fin n → K) (original : R) (i : Fin n) :
    WitnessResult K R n :=
  let primal := decide original
  let side := if primal then original else complement original
  let r := deleteCoordinates (fun s => decide (restrict side s)) ((List.finRange n).erase i) Finset.univ
  let g := generator (restrict side r.1)
  ⟨primal, r.1, fun j => g j / g i, original :: r.2.map (restrict side)⟩

/-- Semantic fidelity of coordinate restriction on a subspace representation. -/
def Restricts (denote : R → Submodule K (Fin n → K)) (restrict : R → Finset (Fin n) → R) : Prop :=
  ∀ u s x, x ∈ denote (restrict u s) ↔ x ∈ denote u ∧ ∀ j, j ∉ s → x j = 0

/-- Dividing a nonzero generator of a line by its marked entry recovers the nonnegative
orientation. This is independent of the pivot order and the initial sign of the generator. -/
theorem normalizeGenerator {W : Submodule K (Fin n → K)} (i : Fin n) (hdim : Module.finrank K W = 1)
    {g c : Fin n → K} (hg : g ∈ W) (hn : g ≠ 0) (hc : c ∈ W) (hc₀ : 0 ≤ c) (hi : 0 < c i) :
    g i ≠ 0 ∧ (fun j => g j / g i) ∈ W ∧ 0 ≤ (fun j => g j / g i) ∧ g i / g i = 1 := by
  have hs : W = K ∙ g := eq_span_singleton_of_mem_of_finrank_eq_one hdim hg hn
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hs ▸ hc)
  have eq j : a * g j = c j := congrFun ha j
  have hgi : g i ≠ 0 := fun h => hi.ne' (by rw [← eq i, h, mul_zero])
  have ha₀ : a ≠ 0 := fun h => hi.ne' (by rw [← eq i, h, zero_mul])
  refine ⟨hgi, ?_, ?_, div_self hgi⟩
  · have heq : (fun j => g j / g i) = (g i)⁻¹ • g := by
      funext j
      exact div_eq_inv_mul _ _
    rw [heq]
    exact W.smul_mem _ hg
  · intro j
    have e : g j / g i = c j / c i := by
      rw [← eq i, ← eq j, mul_div_mul_left _ _ ha₀]
    change 0 ≤ g j / g i
    rw [e]
    exact div_nonneg (hc₀ j) hi.le

/-- With a correct subspace decision and any nonzero generator of a one-dimensional input,
the reduction returns a normalized witness on the actual winning side. The entire transcript,
including the first sign test, has exactly `n` subspace calls. -/
theorem recoverWitness_spec (denote : R → Submodule K (Fin n → K)) (decide : R → Bool)
    (complement : R → R) (restrict : R → Finset (Fin n) → R) (generator : R → Fin n → K)
    (original : R) (i : Fin n)
    (dual : denote (complement original) = (denote original).orthogonalBilin (dotProductBilin K K))
    (cut : Restricts denote restrict)
    (oracle : ∀ r, decide r = true ↔ ∃ x ∈ denote r, 0 ≤ x ∧ 0 < x i)
    (basis : ∀ r, Module.finrank K (denote r) = 1 → (∃ x ∈ denote r, 0 ≤ x ∧ 0 < x i) →
      generator r ∈ denote r ∧ generator r ≠ 0) :
    let result := recoverWitness decide complement restrict generator original i
    let side := if result.primal then original else complement original
    result.queries.length = n ∧ result.primal = decide original ∧
    Module.finrank K (denote (restrict side result.allowed)) = 1 ∧ result.point ∈ denote side ∧
    0 ≤ result.point ∧ result.point i = 1 ∧
    (∀ j, j ∉ result.allowed → result.point j = 0) := by
  let side := if decide original then original else complement original
  let ask := fun s => decide (restrict side s)
  let out := deleteCoordinates ask ((List.finRange n).erase i) Finset.univ
  have win : ∃ x ∈ denote side, 0 ≤ x ∧ 0 < x i := by
    cases h : decide original with
    | true => simpa only [side,h,ite_true] using (oracle original).mp h
    | false =>
      have no : ¬ ∃ x ∈ denote original, 0 ≤ x ∧ 0 < x i := by
        intro h'
        rw [(oracle original).mpr h'] at h
        contradiction
      have win' : ∃ x ∈ (denote original).orthogonalBilin (dotProductBilin K K), 0 ≤ x ∧ 0 < x i := by
        by_contra h'
        exact no ((Farkas.subspace_coordinate_alternative _ _).mpr h')
      simpa only [side,h,Bool.false_eq_true,ite_false,dual] using win'
  have hinit : Finset.univ ∈ witnessSupports (denote side) i := by
    obtain ⟨x, hx, hn, hp⟩ := win
    exact ⟨x,hx,hn,hp,fun j hj => (hj (Finset.mem_univ j)).elim⟩
  have hdec s : ask s = true ↔ s ∈ witnessSupports (denote side) i := by
    rw [show ask s = decide (restrict side s) from rfl, oracle]
    constructor
    · rintro ⟨x,h,nn,pos⟩
      exact ⟨x,((cut side s x).mp h).1,nn,pos,((cut side s x).mp h).2⟩
    · rintro ⟨x,h,nn,pos,supp⟩
      exact ⟨x,(cut side s x).mpr ⟨h,supp⟩,nn,pos⟩
  obtain ⟨hlen,c,hc,hn,hp,hs,hline⟩ := witness_line_in_pred_queries (denote side) i ask hdec hinit
  have hzero (j : Fin n) : c j = 0 ↔ j ∉ out.1 := by simpa [out] using (not_congr (hs j))
  have hid : denote (restrict side out.1) = supportSlice (denote side) c := by
    ext x
    rw [cut]
    change _ ↔ x ∈ denote side ∧ ∀ j, c j = 0 → x j = 0
    simp only [hzero]
  have hdim : Module.finrank K (denote (restrict side out.1)) = 1 := hid ▸ hline
  have hcs : c ∈ denote (restrict side out.1) := (cut _ _ _).mpr ⟨hc,fun j h => (hzero j).mpr h⟩
  obtain ⟨hg,hg₀⟩ := basis _ hdim ⟨c, hcs, hn, hp⟩
  obtain ⟨_, normalized, hnn, hi⟩ := normalizeGenerator i hdim hg hg₀ hcs hn hp
  have endPoint := (cut side out.1 _).mp normalized
  change (original :: out.2.map (restrict side)).length = n ∧ _
  refine ⟨by simpa [out] using hlen,rfl,hdim,endPoint.1,hnn,hi,endPoint.2⟩

/-- Total cost of the actual subspace-query transcript under the per-query bound proved by
`restart_recovery`. This sum observes the work of each request; it does not run requests again. -/
theorem serviceCalls_le (calls : R → ℕ) (qs : List R) (restarts h : ℕ)
    (each : ∀ q ∈ qs, calls q ≤ (restarts + 1) * h) :
    (qs.map calls).sum ≤ qs.length * ((restarts + 1) * h) := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_le_add (each q (by simp)) (ih fun x hx => each x (by simp [hx]))

end Recovery
end LinearProgramming
end Optimization
end OAI
