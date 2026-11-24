import OAI.Computability.VPVNP.ParseIncidenceDefs
import OAI.Computability.VPVNP.HardnessCNF

/-! # Boolean clauses for the local incidence of an ordered parse

Each candidate production has one selection bit. Clauses require a root and both children
of each selected split, exclude ill-typed or conflicting events, and give every nonroot
production a parent. The clauses refer only to selection bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

open HardnessCNF

variable {k : ℕ} {V H : Type*}

private noncomputable def positives (p : Fin k → Prop) : List (Literal k) := by
  classical exact ((List.finRange k).filter (fun i => decide (p i))).map (fun i => (i, true))

private noncomputable def whenClause (p : Prop) (c : List (Literal k)) : CNF k := by
  classical exact if p then [c] else []

private def targets (e : ParseEvent V H) : List (ℕ × ℕ × H) :=
  match e.production with
  | .inl _ => []
  | .inr (b, i, j) => [(e.start, b, i), (e.start + b + 1, e.layer - b - 1, j)]

private theorem mem_targets (e : ParseEvent V H) (l d : ℕ) (h : H) :
    (l, d, h) ∈ targets e ↔ e.Requests l d h := by
  rcases e with ⟨a, t, s, v | ⟨b,i,j⟩⟩ <;> simp [targets, ParseEvent.Requests]

/-- Clauses for a designated root and a finite enumeration of candidate productions. -/
noncomputable def incidenceCNF (event : Fin k → ParseEvent V H) (l d : ℕ) (h : H) : CNF k :=
  [positives (fun i => (event i).Matches l d h)] ++
    (List.finRange k).flatMap fun i =>
      whenClause (¬ (event i).WellFormed) [(i, false)] ++
      ((List.finRange k).flatMap fun j =>
        whenClause ((event i).start = (event j).start ∧ (event i).layer = (event j).layer ∧
          event i ≠ event j) [(i, false), (j, false)]) ++
      ((targets (event i)).map fun t =>
        (i, false) :: positives fun j => (event j).Matches t.1 t.2.1 t.2.2) ++
      whenClause (¬ (event i).Matches l d h) ((i, false) :: positives fun j =>
        (event j).Requests (event i).start (event i).layer (event i).state)

/-- The table whose events have selected flags. -/
noncomputable def selectedEvents (event : Fin k → ParseEvent V H) (x : Fin k → Bool) :
    Finset (ParseEvent V H) := by
  classical exact (Finset.univ.filter fun i => x i = true).image event

@[simp] theorem mem_selectedEvents (event : Fin k → ParseEvent V H) (x : Fin k → Bool)
    (e : ParseEvent V H) : e ∈ selectedEvents event x ↔ ∃ i, x i = true ∧ event i = e := by
  classical simp [selectedEvents]

private def satClause (x : Fin k → Bool) (c : List (Literal k)) : Prop :=
  ∃ a ∈ c, x a.1 = a.2

private theorem sat_positives (p : Fin k → Prop) (x : Fin k → Bool) :
    satClause x (positives p) ↔ ∃ i, p i ∧ x i = true := by
  classical simp [satClause, positives]

private theorem sat_cons_neg (i : Fin k) (c : List (Literal k)) (x : Fin k → Bool) :
    satClause x ((i, false) :: c) ↔ (x i = true → satClause x c) := by
  cases h : x i <;> simp [satClause, h]

private theorem sat_append (p q : CNF k) (x : Fin k → Bool) :
    Satisfies (p ++ q) x ↔ Satisfies p x ∧ Satisfies q x := by
  simp [Satisfies]; aesop

private theorem sat_flatMap {α : Type*} (s : List α) (f : α → CNF k) (x : Fin k → Bool) :
    Satisfies (s.flatMap f) x ↔ ∀ a ∈ s, Satisfies (f a) x := by
  simp [Satisfies]; aesop

private theorem sat_map {α : Type*} (s : List α) (f : α → List (Literal k))
    (x : Fin k → Bool) : Satisfies (s.map f) x ↔ ∀ a ∈ s, satClause x (f a) := by
  simp [Satisfies, satClause]

private theorem sat_single (c : List (Literal k)) (x : Fin k → Bool) :
    Satisfies [c] x ↔ satClause x c := by simp [Satisfies, satClause]

private theorem sat_when (p : Prop) (c : List (Literal k)) (x : Fin k → Bool) :
    Satisfies (whenClause p c) x ↔ (p → satClause x c) := by
  classical by_cases h : p <;> simp [whenClause, h, Satisfies, satClause]

/-- The satisfying assignments select exactly the locally valid tables with the given root. -/
theorem satisfies_incidenceCNF_iff (event : Fin k → ParseEvent V H) (l d : ℕ) (h : H)
    (x : Fin k → Bool) :
    Satisfies (incidenceCNF event l d h) x ↔ IsParseTable (selectedEvents event x) l d h := by
  classical
  simp only [incidenceCNF, sat_append, sat_flatMap, sat_map, sat_single, sat_when,
    sat_cons_neg, sat_positives, List.mem_finRange, true_implies]
  have empty : ¬ satClause x [] := by simp [satClause]
  constructor
  · rintro ⟨⟨r, hr, xr⟩, hy⟩
    constructor
    · exact ⟨event r, (mem_selectedEvents ..).mpr ⟨r, xr, rfl⟩, hr⟩
    · intro e he
      obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
      exact Classical.byContradiction fun hn => empty ((hy i).1.1.1 hn xi)
    · intro e he f hf hs ht
      obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
      obtain ⟨j, xj, rfl⟩ := (mem_selectedEvents ..).mp hf
      exact Classical.byContradiction fun hn => empty ((hy i).1.1.2 j ⟨hs, ht, hn⟩ xi xj)
    · intro e he a t v req
      obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
      obtain ⟨j, hj, xj⟩ := (hy i).1.2 (a,t,v) ((mem_targets ..).mpr req) xi
      exact ⟨event j, (mem_selectedEvents ..).mpr ⟨j, xj, rfl⟩, hj⟩
    · intro e he
      obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
      by_cases hr : (event i).Matches l d h
      · exact Or.inl hr
      · obtain ⟨j, hj, xj⟩ := (hy i).2 hr xi
        exact Or.inr ⟨event j, (mem_selectedEvents ..).mpr ⟨j, xj, rfl⟩, hj⟩
  · intro table
    obtain ⟨e, he, hr⟩ := table.root
    obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
    refine ⟨⟨i, hr, xi⟩, fun i => ?_⟩
    have mem (j : Fin k) (xj : x j = true) := (mem_selectedEvents event x (event j)).mpr ⟨j, xj, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro hn xi
      exact (hn (table.typed _ (mem _ xi))).elim
    · rintro j ⟨hs, ht, hn⟩ xi xj
      exact (hn (table.unique _ (mem _ xi) _ (mem _ xj) hs ht)).elim
    · rintro ⟨a,t,v⟩ hreq xi
      obtain ⟨f, hf, hm⟩ := table.children _ (mem _ xi) a t v ((mem_targets ..).mp hreq)
      obtain ⟨j, xj, rfl⟩ := (mem_selectedEvents ..).mp hf
      exact ⟨j, hm, xj⟩
    · intro hn xi
      obtain ⟨f, hf, hr⟩ := (table.parent _ (mem _ xi)).resolve_left hn
      obtain ⟨j, xj, rfl⟩ := (mem_selectedEvents ..).mp hf
      exact ⟨j, hr, xj⟩



@[simp] private theorem literalCount_zero : literalCount ([] : CNF k) = 0 := rfl

@[simp] private theorem literalCount_singleton (c : List (Literal k)) : literalCount [c] = c.length := by
  simp [literalCount]

private theorem literalCount_append (p q : CNF k) :
    literalCount (p ++ q) = literalCount p + literalCount q := by
  simp [literalCount]

private theorem literalCount_flatMap_le {α : Type*} (xs : List α) (f : α → CNF k) (M : ℕ)
    (h : ∀ a ∈ xs, literalCount (f a) ≤ M) :
    literalCount (xs.flatMap f) ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have hx := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simpa [literalCount_append, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add ha hx

private theorem positives_length_le (p : Fin k → Prop) : (positives p).length ≤ k := by
  classical
  simp only [positives, List.length_map]
  simpa using List.length_filter_le (fun i => decide (p i)) (List.finRange k)

private theorem when_count_le (p : Prop) (c : List (Literal k)) :
    literalCount (whenClause p c) ≤ c.length := by
  classical by_cases h : p <;> simp [whenClause, h]

private theorem child_count_le (e : ParseEvent V H) (i : Fin k)
    (p : ℕ × ℕ × H → Fin k → Prop) :
    literalCount ((targets e).map fun t => (i, false) :: positives (p t)) ≤ 2 * (k + 1) := by
  cases he : e.production with
  | inl _ => simp [targets, he]
  | inr v =>
    obtain ⟨b, j, j'⟩ := v
    simp only [targets, he, List.map_cons, List.map_nil, literalCount, List.length_cons,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    have h₁ := positives_length_le (p (e.start, b, j))
    have h₂ := positives_length_le (p (e.start + b + 1, e.layer - b - 1, j'))
    omega

/-- Quadratic bound on the number of literal occurrences read by the query program. -/
theorem literalCount_incidenceCNF_le (event : Fin k → ParseEvent V H) (l d : ℕ) (h : H) :
    literalCount (incidenceCNF event l d h) ≤ k + k * (5 * k + 4) := by
  classical
  rw [incidenceCNF, literalCount_append, literalCount_singleton]
  apply Nat.add_le_add (positives_length_le _)
  refine (literalCount_flatMap_le _ _ (5 * k + 4) ?_).trans (by simp)
  intro i _
  simp only [literalCount_append]
  have h₁ := when_count_le (¬ (event i).WellFormed) [(i, false)]
  have h₂ := literalCount_flatMap_le (List.finRange k) (fun j =>
    whenClause ((event i).start = (event j).start ∧ (event i).layer = (event j).layer ∧
      event i ≠ event j) [(i, false), (j, false)]) 2
      (fun j _ => when_count_le _ _)
  have h₃ := child_count_le (event i) i (fun t j => (event j).Matches t.1 t.2.1 t.2.2)
  have h₄ := when_count_le (¬ (event i).Matches l d h) ((i, false) :: positives fun j =>
    (event j).Requests (event i).start (event i).layer (event i).state)
  have h₅ := positives_length_le (fun j => (event j).Requests (event i).start
    (event i).layer (event i).state)
  simp only [List.length_cons, List.length_nil, List.length_finRange] at h₁ h₂ h₄
  omega

private theorem length_flatMap_le {α β : Type*} (xs : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ xs, (f a).length ≤ M) : (xs.flatMap f).length ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hx := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h a List.mem_cons_self) hx

private theorem when_length_le (p : Prop) (c : List (Literal k)) : (whenClause p c).length ≤ 1 := by
  classical by_cases h : p <;> simp [whenClause, h]

/-- Guarding each clause costs at most this many extra literals. -/
theorem length_incidenceCNF_le (event : Fin k → ParseEvent V H) (l d : ℕ) (h : H) :
    (incidenceCNF event l d h).length ≤ 1 + k * (k + 4) := by
  classical
  rw [incidenceCNF, List.length_append]
  apply Nat.add_le_add_left
  refine (length_flatMap_le _ _ (k + 4) ?_).trans (by simp)
  intro i _
  simp only [List.length_append, List.length_map]
  have h₁ := when_length_le (¬ (event i).WellFormed) [(i, false)]
  have h₂ := length_flatMap_le (List.finRange k) (fun j =>
    whenClause ((event i).start = (event j).start ∧ (event i).layer = (event j).layer ∧
      event i ≠ event j) [(i, false), (j, false)]) 1
      (fun j _ => when_length_le _ _)
  have h₃ : (targets (event i)).length ≤ 2 := by
    cases he : (event i).production with
    | inl _ => simp [targets, he]
    | inr v => obtain ⟨b,u,v⟩ := v; simp [targets, he]
  have h₄ := when_length_le (¬ (event i).Matches l d h) ((i, false) :: positives fun j =>
    (event j).Requests (event i).start (event i).layer (event i).state)
  simp only [List.length_finRange, Nat.mul_one] at h₂
  omega

end ParseGrammar

end VPVNP
end Computability
end OAI
