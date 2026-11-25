import OAI.Geometry.Hirsch.Word

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Forest

variable {I A J B : Type} {n : ℕ}

theorem induction_path (tree : Forest I A n) (P : I → Prop)
    (root : ∀ i, tree.path i = [] → P i)
    (step : ∀ i j a, tree.path i = (j,a) :: tree.path j → P j → P i) : ∀ i, P i := by
  suffices ∀ k i, (tree.path i).length = k → P i from fun i => this _ i rfl
  intro k
  induction k with
  | zero => exact fun i he => root i (List.length_eq_zero_iff.mp he)
  | succ k ih =>
    intro i he
    cases hp : tree.path i with
    | nil => simp [hp] at he
    | cons entry rest =>
      obtain ⟨j,a⟩ := entry
      rw [← tree.proper _ _ _ _ hp] at hp
      exact step _ _ _ hp (ih j (by simpa [hp] using he))

def push (m : ℕ) (entry : Option B) (rest : List B) : List B :=
  if rest.length < m then entry.toList ++ rest else rest

@[simp] theorem push_none (m : ℕ) (rest : List B) : push m none rest = rest := by
  simp [push]

theorem push_some {m : ℕ} (b : B) {rest : List B} (hh : rest.length < m) :
    push m (some b) rest = b :: rest := by simp [push, hh]

def trace (m : ℕ) (f : A → Option B) : List A → List B
  | [] => []
  | a :: rest => push m (f a) (trace m f rest)

theorem trace_length (m : ℕ) (f : A → Option B) (l : List A) : (trace m f l).length ≤ m := by
  induction l with
  | nil => simp [trace]
  | cons a rest ih =>
    rw [trace, push]
    split
    · cases f a <;> simp_all
    · exact ih

theorem trace_mem {m : ℕ} {f : A → Option B} {l : List A} {b : B}
    (hb : b ∈ trace m f l) : ∃ a ∈ l, f a = some b := by
  induction l with
  | nil => simp [trace] at hb
  | cons a rest ih =>
    have hor : f a = some b ∨ b ∈ trace m f rest := by
      rw [trace, push] at hb
      split at hb
      · simpa using hb
      · exact Or.inr hb
    rcases hor with he | hr
    · exact ⟨a, by simp, he⟩
    · obtain ⟨x,hx,he⟩ := ih hr
      exact ⟨x, List.mem_cons_of_mem _ hx, he⟩

theorem trace_parent (tree : Forest I A n) (m : ℕ) (f : I × A → Option B) :
    ∀ i b rest, trace m f (tree.path i) = b :: rest →
      ∃ j a, f (j,a) = some b ∧ trace m f (tree.path j) = rest := by
  apply tree.induction_path
  · intro i he; simp [he, trace]
  · intro i j a he ih b rest hb
    rw [he, trace, push] at hb
    split at hb
    · cases hf : f (j,a) with
      | none => exact ih _ _ (by simpa [hf] using hb)
      | some v =>
        obtain ⟨rfl,hr⟩ : v = b ∧ trace m f (tree.path j) = rest := by simpa [hf] using hb
        exact ⟨j,a,hf,hr⟩
    · exact ih _ _ hb

theorem trace_past (tree : Forest I A n) (m : ℕ) (f : I × A → Option B) :
    ∀ i j, j ∈ tree.ancestors i → trace m f (tree.path j) ⊆ trace m f (tree.path i) := by
  apply tree.induction_path
  · intro i he j hj
    have : j = i := by simpa [ancestors, he] using hj
    subst j
    exact fun _ hx => hx
  · intro i p a he ih j hj
    rw [ancestors, he, past_cons] at hj
    rcases hj with rfl | hj
    · exact fun _ hx => hx
    · intro x hx
      have hh := ih j hj hx
      rw [he, trace, push]
      split
      · exact List.mem_append_right _ hh
      · exact hh

end OAI.Geometry.Hirsch.Forest
