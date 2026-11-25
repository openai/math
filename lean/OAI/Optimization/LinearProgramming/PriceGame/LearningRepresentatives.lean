import OAI.Optimization.LinearProgramming.PriceGame.LearningConstraints
import OAI.Optimization.LinearProgramming.PriceGame.LearningPaths

/-! # Computing a representative or discarding an empty cell -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning

open Finset

/-- The tightened cell of a finite observation list. -/
def inCell {n} (R : ℕ) (a : Fin n) (os : List (Observation n)) (v : Fin n → ℚ) : Prop :=
  v a = 0 ∧ (∀ i, (boxLower a i : ℚ) ≤ v i ∧ v i ≤ (boxUpper R a i : ℚ)) ∧
    ∀ o ∈ os, accepts o v

/-- Drop a fractional equality or an infeasible difference-constraint system.
The retained table gives the sharp integral upper bound for *every* difference. -/
def cellTable {n} (R : ℕ) (a : Fin n) (os : List (Observation n)) : Option (Paths.Table n) := do
  let d ← addObservations os (boxBounds R a)
  let t := Paths.compute d
  if ∀ i, 0 ≤ Paths.read t i i then some t else none

theorem cellTable_some_iff {n} (R : ℕ) (a : Fin n) (os : List (Observation n)) (t : Paths.Table n) :
    cellTable R a os = some t ↔ ∃ d, addObservations os (boxBounds R a) = some d ∧
      Paths.compute d = t ∧ ∀ i, 0 ≤ Paths.distance d i i := by
  cases h : addObservations os (boxBounds R a) with
  | none => simp [cellTable, h]
  | some d =>
    simp only [cellTable, h, bind, Option.bind_some, Paths.compute_correct, Option.some.injEq,
      exists_eq_left']
    split
    next hd => simp [hd]
    next hd => simp [hd]

private theorem inCell_iff_compiled {n} {R : ℕ} {a : Fin n} {os : List (Observation n)} {d : Bounds n}
    (hd : addObservations os (boxBounds R a) = some d) (v : Fin n → ℚ) :
    inCell R a os v ↔ v a = 0 ∧ respects d v := by
  have hs := addObservations_spec os (boxBounds R a) v
  rw [hd, representedBy_some] at hs
  constructor
  · rintro ⟨ha,hbox,hcuts⟩
    exact ⟨ha,hs.mpr ⟨(boxBounds_spec R a v ha).mpr hbox,hcuts⟩⟩
  · rintro ⟨ha,h⟩
    obtain ⟨hbox,hcuts⟩ := hs.mp h
    exact ⟨ha,(boxBounds_spec R a v ha).mp hbox,hcuts⟩

theorem inCell_iff_table {n} {R : ℕ} {a : Fin n} {os : List (Observation n)} {t : Paths.Table n}
    (ht : cellTable R a os = some t) (v : Fin n → ℚ) :
    inCell R a os v ↔ v a = 0 ∧ respects (Paths.read t) v := by
  obtain ⟨d,hd,rfl,_hdiag⟩ := (cellTable_some_iff _ _ _ _).mp ht
  rw [inCell_iff_compiled hd, Paths.compute_correct]
  exact and_congr_right fun _ => ⟨fun h => Paths.feasible_distance h,
    fun h i j => (h i j).trans (by exact_mod_cast Paths.distance_le d i j)⟩

/-- Every integral point with the observed three-way comparisons survives the compilation. -/
theorem cellTable_iff_integer {n} (R : ℕ) (a : Fin n) (os : List (Observation n)) :
    (∃ t, cellTable R a os = some t) ↔
    ∃ v : Fin n → ℤ, v a = 0 ∧ (∀ i, boxLower a i ≤ v i ∧ v i ≤ boxUpper R a i) ∧
      ∀ o ∈ os, realizes o (fun i => (v i : ℚ)) := by
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨d,hd,_,hdiag⟩ := (cellTable_some_iff _ _ _ _).mp ht
    obtain ⟨v,ha,hv⟩ := (Paths.feasible_iff_diagonal d a).mpr hdiag
    have hc : inCell R a os (fun i => (v i : ℚ)) :=
      (inCell_iff_compiled hd _).mpr ⟨by simp [ha], fun i j => by dsimp only; exact_mod_cast hv i j⟩
    exact ⟨v,ha,fun i => by have h := hc.2.1 i; dsimp only at h; exact_mod_cast h,
      fun o ho => accepts_sound (hc.2.2 o ho)⟩
  · rintro ⟨v,ha,hbox,hcuts⟩
    let q (i : Fin n) : ℚ := (v i : ℚ)
    have hqa : q a = 0 := by simp [q,ha]
    have hb : respects (boxBounds R a) q := (boxBounds_spec R a _ hqa).mpr
      (fun i => by dsimp only [q]; exact_mod_cast hbox i)
    have hc := (addObservations_spec os (boxBounds R a) q).mpr ⟨hb,
      fun o ho => (accepts_integer o v).mpr (hcuts o ho)⟩
    obtain ⟨d,hd,hv⟩ := hc
    exact ⟨_,(cellTable_some_iff _ _ _ _).mpr ⟨d,hd,rfl,Paths.feasible_diagonal hv⟩⟩

section Representation

variable {p R : ℕ} {a : Fin (p+1)} {os : List (Observation (p+1))} {t : Paths.Table (p+1)}

lemma cellTable_geometry (ht : cellTable R a os = some t) :
    (∀ i, Paths.read t i i = 0) ∧
    ∀ s i j, Paths.read t s j ≤ Paths.read t s i + Paths.read t i j := by
  obtain ⟨d,_,rfl,hdiag⟩ := (cellTable_some_iff _ _ _ _).mp ht
  rw [Paths.compute_correct]
  exact ⟨Paths.distance_diag d hdiag, fun s i j => Paths.distance_triangle d hdiag i s j⟩

/-- The representative actually returned for each feasible array. -/
def cellRepresentative (R : ℕ) (a : Fin (p+1)) (os : List (Observation (p+1))) :
    Option (Fin (p+1) → ℚ) :=
  (cellTable R a os).map fun t => representative (Paths.read t) a

theorem representative_inCell (ht : cellTable R a os = some t) :
    inCell R a os (representative (Paths.read t) a) := by
  refine (inCell_iff_table ht _).mpr ⟨representative_anchor a,?_⟩
  intro i j
  rw [representative_difference]
  apply (div_le_iff₀ (by positivity : 0 < ((p + 1 : ℕ) : ℚ))).mpr
  calc
    _ ≤ ∑ _ : Fin (p+1), (Paths.read t i j : ℚ) := by
      apply sum_le_sum; intro s _
      exact_mod_cast (potential_bounds (cellTable_geometry ht).2 a j i s).2
    _ = _ := by simp [mul_comm]

theorem cellRepresentative_sound {v : Fin (p+1) → ℚ} (h : cellRepresentative R a os = some v) :
    v a = 0 ∧ (∀ i, (boxLower a i : ℚ) ≤ v i ∧ v i ≤ (boxUpper R a i : ℚ)) ∧
      ∀ o ∈ os, realizes o v := by
  cases ht : cellTable R a os with
  | none => simp [cellRepresentative,ht] at h
  | some t =>
    simp [cellRepresentative,ht] at h
    subst v
    have hc := representative_inCell ht
    exact ⟨hc.1,hc.2.1,fun o ho => accepts_sound (hc.2.2 o ho)⟩

/-- All feature values in the cell lie between the two integer endpoints; the source
potentials attain them. This includes diagonal features and features using the dummy. -/
theorem feature_range (ht : cellTable R a os = some t) (i j : Fin (p+1)) :
    (∀ v, inCell R a os v →
      (-(Paths.read t i j : ℚ) ≤ v i - v j ∧ v i - v j ≤ (Paths.read t j i : ℚ))) ∧
    (∃ v, inCell R a os v ∧ v i - v j = -(Paths.read t i j : ℚ)) ∧
      ∃ v, inCell R a os v ∧ v i - v j = (Paths.read t j i : ℚ) := by
  obtain ⟨hdiag,htri⟩ := cellTable_geometry ht
  have hpot (s) : inCell R a os (fun i => (potential (Paths.read t) a s i : ℚ)) := by
    apply (inCell_iff_table ht _).mpr
    exact ⟨by simp [potential],fun i j => by dsimp only; exact_mod_cast (potential_bounds htri a j i s).2⟩
  obtain ⟨hi,hj⟩ := potential_extremes hdiag a i j
  refine ⟨?_, ⟨_,hpot i,by exact_mod_cast hi⟩, ⟨_,hpot j,by exact_mod_cast hj⟩⟩
  intro v hv
  have h := ((inCell_iff_table ht v).mp hv).2
  exact ⟨by linarith [h i j],h j i⟩

end Representation

end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
