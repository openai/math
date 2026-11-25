import Mathlib.Data.Nat.Basic

/-! # Passing a tape block between consecutive uses in a fixed trace -/

namespace OAI.Computability.MultitapeWeakETH

namespace BlockHistory

variable {I B Q : Type*} (uses : ℕ → I → Prop) [∀ t i, Decidable (uses t i)]

abbrev Active (t : ℕ) := {i // uses t i}

/-- Index of the last epoch that supplied the block before the given time. -/
def previous : ℕ → I → Option ℕ
  | 0, _ => none
  | t+1, i => if uses t i then some t else previous t i

theorem previous_eq_some {t j : ℕ} {i : I} :
    previous uses t i = some j ↔ j < t ∧ uses j i ∧ ∀ u, j < u → u < t → ¬uses u i := by
  induction t with
  | zero => simp [previous]
  | succ t ih =>
    by_cases here : uses t i
    · simp only [previous,ite_eq_left here,Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨by omega,here,fun u l h => by omega⟩
      · rintro ⟨lt,_,last⟩
        by_contra ne
        exact last t (by omega) (by omega) here
    · rw [previous,ite_eq_right here,ih]
      constructor
      · rintro ⟨lt,used,last⟩
        exact ⟨by omega,used,fun u lo hi => by
          by_cases hu : u = t
          · simpa [hu] using here
          · exact last u lo (by omega)⟩
      · rintro ⟨lt,used,last⟩
        have ne : j ≠ t := fun eq => here (eq ▸ used)
        exact ⟨by omega,used,fun u lo hi => last u lo (by omega)⟩

/-- At most one later epoch can consume a given block from the same producer. -/
theorem unique_consumer {j t u : ℕ} {i : I} (ht : uses t i) (hu : uses u i)
    (a : previous uses t i = some j) (b : previous uses u i = some j) : t = u := by
  obtain ⟨jt,_,endT⟩ := (previous_eq_some uses).mp a
  obtain ⟨ju,_,endU⟩ := (previous_eq_some uses).mp b
  rcases lt_trichotomy t u with h | h | h
  · exact (endU t jt h ht).elim
  · exact h
  · exact (endT u ju h hu).elim

/-- A wire value is either an initial symbol or the output label of its
unique previous producer. The local witness supplies labels only on used blocks. -/
def readWire (init : I → B) (labels : (t : ℕ) → Active uses t → B) : ℕ → I → B
  | 0, i => init i
  | t+1, i => if h : uses t i then labels t ⟨i,h⟩ else readWire init labels t i

theorem readWire_succ (init : I → B) (labels : (t : ℕ) → Active uses t → B)
    (t : ℕ) (i : I) : readWire uses init labels (t+1) i =
      if h : uses t i then labels t ⟨i,h⟩ else readWire uses init labels t i := rfl

theorem readWire_from_previous (init : I → B) (labels : (t : ℕ) → Active uses t → B)
    {t j : ℕ} {i : I} (h : previous uses t i = some j) :
    readWire uses init labels t i = labels j ⟨i,((previous_eq_some uses).mp h).2.1⟩ := by
  induction t with
  | zero => simp [previous] at h
  | succ t ih =>
    by_cases used : uses t i
    · simp only [previous,ite_eq_left used,Option.some.injEq] at h
      subst j
      simp [readWire_succ,used]
    · simp only [previous,ite_eq_right used] at h
      simpa [readWire_succ,used] using ih h

/-- Satisfaction of the epoch relations using only incident wires is equivalent
to a globally consistent memory history, including blocks never touched. -/
theorem glue_iff (init final : I → B) (control : ℕ → Q) (epochs : ℕ)
    (legal : (t : ℕ) → Q → (Active uses t → B) → Q → (Active uses t → B) → Prop) :
    (∃ labels : (t : ℕ) → Active uses t → B,
      (∀ t < epochs, legal t (control t) (fun i => readWire uses init labels t i.1)
        (control (t+1)) (labels t)) ∧ readWire uses init labels epochs = final) ↔
    ∃ mem : ℕ → I → B, mem 0 = init ∧ mem epochs = final ∧
      ∀ t < epochs, legal t (control t) (fun i => mem t i.1) (control (t+1))
          (fun i => mem (t+1) i.1) ∧ ∀ i, ¬uses t i → mem (t+1) i = mem t i := by
  constructor
  · rintro ⟨labels,h,done⟩
    refine ⟨readWire uses init labels,rfl,done,fun t lt => ⟨?_,?_⟩⟩
    · simpa only [readWire_succ,dite_eq_left (Subtype.property _)] using h t lt
    · intro i hu
      simp [readWire_succ,hu]
  · rintro ⟨mem,start,done,step⟩
    let labels (t : ℕ) (i : Active uses t) := mem (t+1) i.1
    have track (t : ℕ) (ht : t ≤ epochs) : readWire uses init labels t = mem t := by
      induction t with
      | zero => exact start.symm
      | succ t ih =>
        funext i
        rw [readWire_succ]
        by_cases used : uses t i
        · simp [used,labels]
        · simp only [used,↓reduceDIte,ih (by omega)]
          exact ((step t (by omega)).2 i used).symm
    refine ⟨labels,fun t ht => ?_,(track epochs le_rfl).trans done⟩
    rw [track t (by omega)]
    exact (step t ht).1

end BlockHistory
end OAI.Computability.MultitapeWeakETH
