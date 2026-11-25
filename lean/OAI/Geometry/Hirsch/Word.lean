import OAI.Geometry.Hirsch.Forest

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Forest

abbrev Word (Choice : Type) (height : ℕ) := {word : List Choice // word.length ≤ height}

namespace Word

variable {Choice : Type} {height : ℕ}

def code (word : Word Choice height) (idx : Fin height) := word.val[idx.val]?

theorem injective : Function.Injective (code (Choice := Choice) (height := height)) := by
  intro first last he
  apply Subtype.ext
  apply List.ext_getElem?
  intro idx
  by_cases hi : idx < height
  · exact congrFun he ⟨idx, hi⟩
  · rw [List.getElem?_eq_none (first.property.trans (le_of_not_gt hi)),
      List.getElem?_eq_none (last.property.trans (le_of_not_gt hi))]

instance [Finite Choice] : Finite (Word Choice height) := Finite.of_injective code injective
instance [Finite Choice] : Fintype (Word Choice height) := Fintype.ofFinite _

theorem size [Fintype Choice] : Fintype.card (Word Choice height) ≤ (Fintype.card Choice + 1)^height := by
  simpa using Fintype.card_le_of_injective (code (Choice := Choice) (height := height)) injective

def route : (word : List Choice) → word.length ≤ height → List (Word Choice height × Choice)
  | [], _ => []
  | opt :: rest, hh => (⟨rest, by simpa using Nat.le_of_succ_le hh⟩, opt) ::
      route rest (by simpa using Nat.le_of_succ_le hh)

@[simp] theorem route_length (word : List Choice) (hh : word.length ≤ height) :
    (route word hh).length = word.length := by
  induction word <;> simp [route, *]

def tree (Choice : Type) (height : ℕ) : Forest (Word Choice height) Choice height where
  path word := route word.val word.property
  proper := by
    rintro ⟨_ | ⟨opt, rest⟩, hh⟩ parent label tail he
    · simp [route] at he
    · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := List.cons.inj he
      rfl
  bounded word := by simpa using word.property

theorem nonempty_of_viable {usable : Set (Word Choice height)}
    (hv : (tree Choice height).Viable usable) : usable.Nonempty := by
  obtain ⟨pick, hp⟩ := hv
  by_contra hn
  have hex : ∀ len ≤ height, ∃ word : Word Choice height,
      Live usable pick ((tree Choice height).path word) ∧ word.val.length = len := by
    intro len
    induction len with
    | zero => exact fun _ => ⟨⟨[], by simp⟩, live_nil usable pick, rfl⟩
    | succ len ih =>
      intro hh
      obtain ⟨word, hw, he⟩ := ih (by omega)
      refine ⟨⟨pick word :: word.val, by simpa [he]⟩, ?_, by simp [he]⟩
      exact (live_cons ..).mpr ⟨fun hi => hn ⟨word, hi⟩, rfl, hw⟩
  obtain ⟨word, hw, he⟩ := hex height le_rfl
  exact hn ⟨word, hp word hw (by simpa [tree] using he)⟩

end Word

theorem tracer (Choice : Type) [Fintype Choice] [Nonempty Choice] (height limit : ℕ) :
    (bank Choice height).Tracer limit ((limit + 1) * (Fintype.card Choice + 1)^height) (height + 1) := by
  let seq := fun _ : Fin (limit + 1) => Word.tree Choice height
  let tree := join seq
  refine ⟨tree.program, tree.accepts, ?_, ?_, tree.ancestors_bound⟩
  · intro usable hv
    have hh := (join_viable seq usable).mp hv
    choose coord hc using fun idx => Word.nonempty_of_viable (hh idx)
    let fn := fun idx => (⟨idx, coord idx⟩ : tree.program.Coord)
    have hi : Function.Injective fn := fun _ _ he => congrArg Sigma.fst he
    have hle := ncard_le_ncard_of_injOn fn (s := univ) (t := usable) (fun idx _ => hc idx) hi.injOn
    simpa using hle
  · change Fintype.card (Σ _ : Fin (limit + 1), Word Choice height) ≤ _
    simpa using Nat.mul_le_mul_left (limit + 1) (Word.size (Choice := Choice) (height := height))

end OAI.Geometry.Hirsch.Forest
