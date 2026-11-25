import OAI.Optimization.LinearProgramming.PriceGame.Learning

/-! # Compiling observations to integer difference constraints -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning

/-- The inequality stored at `(i,j)` is `v j - v i ≤ d i j`. -/
abbrev Bounds (n : ℕ) := Fin n → Fin n → ℤ

/-- The three-way comparison for one observed feature `v i - v j`. -/
structure Observation (n : ℕ) where
  i : Fin n
  j : Fin n
  threshold : ℚ
  side : Ordering
  deriving DecidableEq

def respects {n} (d : Bounds n) (v : Fin n → ℚ) : Prop :=
  ∀ i j, v j - v i ≤ (d i j : ℚ)

def accepts {n} (o : Observation n) (v : Fin n → ℚ) : Prop :=
  tightenedCut o.side o.threshold (v o.i - v o.j)

def realizes {n} (o : Observation n) (v : Fin n → ℚ) : Prop :=
  compare (v o.i - v o.j) o.threshold = o.side

lemma accepts_sound {n} {o : Observation n} {v : Fin n → ℚ} (h : accepts o v) :
    realizes o v := tightenedCut_sound _ _ _ h

lemma accepts_integer {n} (o : Observation n) (v : Fin n → ℤ) :
    accepts o (fun i => (v i : ℚ)) ↔ realizes o (fun i => (v i : ℚ)) := by
  simpa [accepts, realizes, Int.cast_sub] using tightenedCut_int_iff o.side o.threshold (v o.i - v o.j)

/-- Intersect one directed inequality with the system. -/
def tightenArc {n} (d : Bounds n) (i j : Fin n) (c : ℤ) : Bounds n :=
  fun s t => if s = i ∧ t = j then min (d s t) c else d s t

lemma respects_tightenArc {n} (d : Bounds n) (v : Fin n → ℚ) (i j : Fin n) (c : ℤ) :
    respects (tightenArc d i j c) v ↔ respects d v ∧ v j - v i ≤ c := by
  constructor
  · intro h
    have bound (s t) : tightenArc d i j c s t ≤ d s t := by
      simp only [tightenArc]; split <;> simp
    refine ⟨fun s t => (h s t).trans (by exact_mod_cast bound s t), ?_⟩
    have hc : tightenArc d i j c i j ≤ c := by simp [tightenArc]
    exact (h i j).trans (by exact_mod_cast hc)
  · rintro ⟨h,hc⟩ s t
    by_cases heq : s = i ∧ t = j
    · obtain ⟨rfl,rfl⟩ := heq
      simpa [tightenArc, Int.cast_min] using le_min (h s t) hc
    · simpa [tightenArc, heq] using h s t

/-- An equality to a fractional threshold discards the candidate cell. -/
def addObservation {n} (d : Bounds n) (o : Observation n) : Option (Bounds n) :=
  match o.side with
  | .lt => some (tightenArc d o.j o.i (⌈o.threshold⌉ - 1))
  | .gt => some (tightenArc d o.i o.j (-(⌊o.threshold⌋ + 1)))
  | .eq => if o.threshold = (⌊o.threshold⌋ : ℤ) then
      some (tightenArc (tightenArc d o.j o.i ⌊o.threshold⌋) o.i o.j (-⌊o.threshold⌋))
    else none

def representedBy {n} (result : Option (Bounds n)) (v : Fin n → ℚ) : Prop :=
  ∃ d, result = some d ∧ respects d v

@[simp] lemma representedBy_some {n} (d : Bounds n) (v : Fin n → ℚ) :
    representedBy (some d) v ↔ respects d v := by simp [representedBy]

@[simp] lemma representedBy_none {n} (v : Fin n → ℚ) : ¬ representedBy none v := by
  simp [representedBy]

lemma addObservation_spec {n} (d : Bounds n) (v : Fin n → ℚ) (o : Observation n) :
    representedBy (addObservation d o) v ↔ respects d v ∧ accepts o v := by
  cases o with
  | mk i j θ side =>
    cases side with
    | lt => simp [addObservation, accepts, tightenedCut, respects_tightenArc]
    | gt =>
      simp only [addObservation, representedBy_some, respects_tightenArc, accepts, tightenedCut,
        Int.cast_neg, and_congr_right_iff]
      intro _; constructor <;> intro h <;> linarith
    | eq =>
      simp only [addObservation, accepts, tightenedCut]
      split
      next hi =>
        rw [representedBy_some, respects_tightenArc, respects_tightenArc, Int.cast_neg]
        constructor
        · rintro ⟨⟨h,hu⟩,hl⟩; exact ⟨h, by linarith, hi⟩
        · rintro ⟨h,he,_⟩; exact ⟨⟨h,by linarith⟩,by linarith⟩
      next hi => simp [hi]

/-- Apply the observations sequentially, retaining only the strongest arc on each pair. -/
def addObservations {n} : List (Observation n) → Bounds n → Option (Bounds n)
  | [], d => some d
  | o :: os, d => (addObservation d o).bind (addObservations os)

theorem addObservations_spec {n} (os : List (Observation n)) (d : Bounds n) (v : Fin n → ℚ) :
    representedBy (addObservations os d) v ↔ respects d v ∧ ∀ o ∈ os, accepts o v := by
  induction os generalizing d with
  | nil => simp [addObservations]
  | cons o os ih =>
    have h := addObservation_spec d v o
    cases he : addObservation d o with
    | none =>
      simp [he] at h
      rw [addObservations, he]
      apply iff_of_false (representedBy_none v)
      rintro ⟨hd,hall⟩
      exact h hd (hall o (by simp))
    | some e =>
      simp only [he, representedBy_some] at h
      simp [addObservations, he, ih, h, and_assoc]

/-- Original integer box, with a dummy vertex fixed at zero. -/
def boxLower {n} (a i : Fin n) : ℤ := if i = a then 0 else 1

def boxUpper {n} (R : ℕ) (a i : Fin n) : ℤ := if i = a then 0 else (R : ℤ) + 1

def boxBounds {n} (R : ℕ) (a : Fin n) : Bounds n :=
  fun s t => if s = t then 0 else boxUpper R a t - boxLower a s

theorem boxBounds_spec {n} (R : ℕ) (a : Fin n) (v : Fin n → ℚ) (ha : v a = 0) :
    respects (boxBounds R a) v ↔ ∀ i, (boxLower a i : ℚ) ≤ v i ∧ v i ≤ (boxUpper R a i : ℚ) := by
  constructor
  · intro h i
    by_cases hi : i = a
    · subst i; simp [boxLower, boxUpper, ha]
    · have lower := h i a
      have upper := h a i
      simp [boxBounds, hi, Ne.symm hi, boxLower, boxUpper, ha] at lower upper ⊢
      exact ⟨by linarith, upper⟩
  · intro h i j
    by_cases hij : i = j
    · subst j; simp [boxBounds]
    · simp [boxBounds, hij]
      linarith [(h i).1, (h j).2]

end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
