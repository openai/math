import OAI.Computability.VPVNP.SlotGraph
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Function.Basic

/-!
# The indexed greedy scans for Appendix C

An indexed base admits deterministic choices of all colors and offsets.
Each scan visits the base in increasing index order. It stores one label
per vertex and selects the first index outside the bounded list of
forbidden values at that vertex. The two scans provide the first local
record construction in Appendix E of *VP and VNP differ over every field*.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

variable {V : Type*} {d : ℕ}

/-- The list of increments in Appendix C's `Lₓ`: zero and the tag
displacements of all the outgoing slots. Repeated values are harmless. -/
def tagIncrement {Tag : Type*} [Zero Tag] (τ : V × Fin d → Tag) (x : V) :
    Option (Fin d) → Tag
  | none => 0
  | some i => τ (x, i)

namespace SlotGraph

variable (G : SlotGraph V d) {N : ℕ}

/-- The tag exclusions imposed at both incidences of each arc in Appendix C. -/
def ValidTagOffsets {Tag : Type*} [AddCommGroup Tag] (τ : V × Fin d → Tag) (φ : V → Tag) : Prop :=
  ∀ e, (∀ a, φ e.1 ≠ τ e + tagIncrement τ e.1 a) ∧
    (∀ b, φ (G.target e).1 ≠ τ e + tagIncrement τ (G.target e).1 b) ∧
    ∀ a b, φ e.1 + φ (G.target e).1 ≠
      τ e + tagIncrement τ e.1 a + tagIncrement τ (G.target e).1 b

/-- Take the least candidate index absent from the forbidden list. -/
private def firstMissing {I : Type*} [Fintype I] {J : ℕ}
    (f : I → Fin J) (hcard : Fintype.card I < J) : {j : Fin J // ∀ i, j ≠ f i} := by
  let choices := Finset.univ \ Finset.univ.image f
  have hn : choices.Nonempty := by
    by_contra! h
    have hs : Function.Surjective f := by
      intro j
      have hj : j ∉ choices := by simp [h]
      simpa [choices] using hj
    exact hcard.not_ge (by simpa using Fintype.card_le_of_surjective f hs)
  refine ⟨choices.min' hn, ?_⟩
  have h := (Finset.mem_sdiff.mp (choices.min'_mem hn)).2
  intro i hi
  exact h (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩)

private theorem firstMissing_earlier {I : Type*} [Fintype I] {J : ℕ}
    (f : I → Fin J) (hcard : Fintype.card I < J) (k : Fin J)
    (hk : k < (firstMissing f hcard).1) : ∃ i, f i = k := by
  by_contra! h
  have hm : k ∈ Finset.univ \ Finset.univ.image f := by simp [h]
  exact hk.not_ge (Finset.min'_le _ _ hm)

private def lookup {A : Type*} (order : V ≃ Fin N) (labels : Vector A N) (x : V) : A :=
  labels[(order x).val]

private def visit {A : Type*} (order : V ≃ Fin N) (select : V → (V → A) → A)
    (labels : Vector A N) (i : Fin N) : Vector A N :=
  labels.set i (select (order.symm i) (lookup order labels))

private def scan {A : Type*} (order : V ≃ Fin N) (init : A) (select : V → (V → A) → A) : V → A :=
  lookup order ((List.finRange N).foldl (visit order select) (Vector.replicate N init))

private def goodOn {A : Type*} (allowed : V → A → Prop)
    (compatible : V × Fin d → A → A → Prop) (s : V → Prop) (f : V → A) : Prop :=
  (∀ x, s x → allowed x (f x)) ∧
    ∀ e, s e.1 → s (G.target e).1 → compatible e (f e.1) (f (G.target e).1)

private theorem update_good {A : Type*} [DecidableEq V] {allowed : V → A → Prop}
    {compatible : V × Fin d → A → A → Prop} {s : V → Prop} {f : V → A}
    (hf : G.goodOn allowed compatible s f) {x : V} {a : A} (hu : allowed x a)
    (hout : ∀ i, compatible (x, i) a (f (G.target (x, i)).1))
    (hin : ∀ i, compatible (G.target.symm (x, i)) (f (G.target.symm (x, i)).1) a) :
    G.goodOn allowed compatible (fun y ↦ y = x ∨ s y) (Function.update f x a) := by
  constructor
  · intro y hy
    by_cases h : y = x
    · subst y
      simpa using hu
    · rw [Function.update_of_ne h]
      exact hf.1 y (hy.resolve_left h)
  · rintro ⟨y, i⟩ hy hz
    by_cases h : y = x
    · subst y
      rw [Function.update_self, Function.update_of_ne (G.ends_ne (x, i))]
      exact hout i
    · rw [Function.update_of_ne h]
      by_cases hz' : (G.target (y, i)).1 = x
      · rw [hz', Function.update_self]
        have eqn : G.target (y, i) = (x, (G.target (y, i)).2) := Prod.ext hz' rfl
        simpa only [← eqn, Equiv.symm_apply_apply] using hin (G.target (y, i)).2
      · rw [Function.update_of_ne hz']
        exact hf.2 (y, i) (hy.resolve_left h) (hz.resolve_left hz')

/-- One visit updates just the selected vertex of the partial label table. -/
def orderedUpdate {A : Type*} [DecidableEq V] (order : V ≃ Fin N)
    (select : V → (V → A) → A) (f : V → A) (i : Fin N) : V → A :=
  Function.update f (order.symm i) (select (order.symm i) f)

private theorem lookup_visit {A : Type*} [DecidableEq V] (order : V ≃ Fin N)
    (select : V → (V → A) → A) (labels : Vector A N) (i : Fin N) :
    lookup order (visit order select labels i) = orderedUpdate order select (lookup order labels) i := by
  funext y
  by_cases hy : y = order.symm i
  · subst y
    simp [lookup, visit, orderedUpdate]
  · have hi : i.val ≠ (order y).val := fun h ↦ hy (order.eq_symm_apply.mpr (Fin.ext h.symm))
    simp [visit, lookup, hi, orderedUpdate, Function.update_of_ne hy]

private theorem scan_eq_fold {A : Type*} [DecidableEq V] (order : V ≃ Fin N)
    (init : A) (select : V → (V → A) → A) :
    scan order init select = (List.finRange N).foldl (orderedUpdate order select) (fun _ ↦ init) := by
  have fold (ids : List (Fin N)) (labels : Vector A N) :
      lookup order (ids.foldl (visit order select) labels) =
        ids.foldl (orderedUpdate order select) (lookup order labels) := by
    induction ids generalizing labels with
    | nil => rfl
    | cons i ids ih => simp only [List.foldl_cons, ih, lookup_visit]
  rw [scan, fold]
  congr 1
  funext x
  simp [lookup]

private theorem scan_valid {A : Type*} (order : V ≃ Fin N) (init : A) (select : V → (V → A) → A)
    (allowed : V → A → Prop) (compatible : V × Fin d → A → A → Prop)
    (step : ∀ x f, allowed x (select x f) ∧
      (∀ i, compatible (x, i) (select x f) (f (G.target (x, i)).1)) ∧
      (∀ i, compatible (G.target.symm (x, i)) (f (G.target.symm (x, i)).1) (select x f))) :
    (∀ x, allowed x (scan order init select x)) ∧
      ∀ e, compatible e (scan order init select e.1) (scan order init select (G.target e).1) := by
  classical
  have walk (ids : List (Fin N)) (s : V → Prop) (labels : Vector A N)
      (hs : G.goodOn allowed compatible s (lookup order labels)) :
      G.goodOn allowed compatible (fun x ↦ order x ∈ ids ∨ s x)
        (lookup order (ids.foldl (visit order select) labels)) := by
    induction ids generalizing s labels with
    | nil => simpa only [List.foldl_nil, List.not_mem_nil, false_or] using hs
    | cons i ids ih =>
      obtain ⟨hu, hout, hin⟩ := step (order.symm i) (lookup order labels)
      have h := G.update_good hs hu hout hin
      change G.goodOn _ _ _ (orderedUpdate order select (lookup order labels) i) at h
      rw [← lookup_visit order select] at h
      have ht := ih _ _ h
      simpa only [List.foldl_cons, List.mem_cons, order.eq_symm_apply,
        or_assoc, or_left_comm] using ht
  have h := walk (List.finRange N) (fun _ ↦ False) (Vector.replicate N init)
    (by simp [goodOn])
  exact ⟨fun x ↦ h.1 x (Or.inl (List.mem_finRange _)),
    fun e ↦ h.2 e (Or.inl (List.mem_finRange _)) (Or.inl (List.mem_finRange _))⟩

/-- The colors currently stored at the outgoing and incoming neighbors of a vertex, indexed by
direction and slot number. -/
def colorForbidden (x : V) (f : V → Fin (2 * d + 1)) : Bool × Fin d → Fin (2 * d + 1)
  | (true, i) => f (G.target (x, i)).1
  | (false, i) => f (G.target.symm (x, i)).1

/-- Least permissible color at a vertex of a partially filled table. -/
def chooseColor (x : V) (f : V → Fin (2 * d + 1)) : Fin (2 * d + 1) :=
  (firstMissing (G.colorForbidden x f) (by simp)).1

theorem chooseColor_spec (x : V) (f : V → Fin (2 * d + 1)) :
    (∀ t, G.chooseColor x f ≠ G.colorForbidden x f t) ∧
    (∀ k < G.chooseColor x f, ∃ t, G.colorForbidden x f t = k) :=
  ⟨(firstMissing (G.colorForbidden x f) (by simp)).2,
    firstMissing_earlier (G.colorForbidden x f) (by simp)⟩

/-- Select a proper coloring by visiting the indexed base once, reading
only colors at the two lists of neighboring endpoints. -/
def orderedColor (order : V ≃ Fin N) : V → Fin (2 * d + 1) :=
  scan order 0 G.chooseColor

theorem orderedColor_fold [DecidableEq V] (order : V ≃ Fin N) :
    G.orderedColor order = (List.finRange N).foldl (orderedUpdate order G.chooseColor) (fun _ ↦ 0) :=
  scan_eq_fold order 0 G.chooseColor

theorem orderedColor_proper (order : V ≃ Fin N) (e : V × Fin d) :
    G.orderedColor order e.1 ≠ G.orderedColor order (G.target e).1 := by
  let select (x : V) (f : V → Fin (2 * d + 1)) := (firstMissing (G.colorForbidden x f) (by simp)).1
  have h := G.scan_valid order 0 select (fun _ _ ↦ True) (fun _ a b ↦ a ≠ b) (fun x f ↦
    ⟨trivial, fun i ↦ (firstMissing (G.colorForbidden x f) (by simp)).2 (true, i),
      fun i ↦ ((firstMissing (G.colorForbidden x f) (by simp)).2 (false, i)).symm⟩)
  exact h.2 e

variable {Tag : Type*} [AddCommGroup Tag] {J : ℕ}

/-- Indices for the forbidden-tag tests, recording an incident arc and either one local
increment or a pair of endpoint increments. -/
abbrev TagTests (d : ℕ) :=
  (Bool × Fin d) × (Option (Fin d) ⊕ (Option (Fin d) × Option (Fin d)))

/-- Compute the excluded tag for one incident-arc test from its displacement and the specified
increments, using the neighboring tag assignment in the two-endpoint case. -/
def tagForbidden (τ : V × Fin d → Tag) (x : V) (f : V → Tag) : TagTests d → Tag
  | ((true, i), .inl a) => τ (x, i) + tagIncrement τ x a
  | ((false, i), .inl a) => τ (G.target.symm (x, i)) + tagIncrement τ x a
  | ((true, i), .inr (a, b)) =>
    let y := (G.target (x, i)).1
    τ (x, i) + tagIncrement τ x a + tagIncrement τ y b - f y
  | ((false, i), .inr (a, b)) =>
    let e := G.target.symm (x, i)
    τ e + tagIncrement τ e.1 a + tagIncrement τ x b - f e.1

/-- Choose the least indexed tag outside the forbidden list for the current vertex and partial
tag assignment. -/
def chooseTag (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) (x : V) (f : V → Tag) : Tag :=
  index.symm (firstMissing (index ∘ G.tagForbidden τ x f)
    (by simpa [TagTests, pow_two] using hcard)).1

theorem chooseTag_spec (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) (x : V) (f : V → Tag) :
    (∀ t, index (G.chooseTag index τ hcard x f) ≠ index (G.tagForbidden τ x f t)) ∧
    (∀ k < index (G.chooseTag index τ hcard x f), ∃ t, index (G.tagForbidden τ x f t) = k) := by
  unfold chooseTag
  rw [Equiv.apply_symm_apply]
  exact ⟨(firstMissing (index ∘ G.tagForbidden τ x f)
    (by simpa [TagTests, pow_two] using hcard)).2,
    firstMissing_earlier (index ∘ G.tagForbidden τ x f) _⟩

/-- Select tag offsets in one indexed base scan. Every step examines a
list of at most `2d((d+1)+(d+1)²)` forbidden indices, counting duplicates. -/
def orderedTagOffsets (order : V ≃ Fin N) (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) : V → Tag :=
  scan order 0 (G.chooseTag index τ hcard)

theorem orderedTagOffsets_fold [DecidableEq V] (order : V ≃ Fin N) (index : Tag ≃ Fin J)
    (τ : V × Fin d → Tag) (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) :
    G.orderedTagOffsets order index τ hcard =
      (List.finRange N).foldl (orderedUpdate order (G.chooseTag index τ hcard)) (fun _ ↦ 0) :=
  scan_eq_fold order 0 (G.chooseTag index τ hcard)

theorem orderedTagOffsets_valid (order : V ≃ Fin N) (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) :
    G.ValidTagOffsets τ (G.orderedTagOffsets order index τ hcard) := by
  let allowed (x : V) (t : Tag) := ∀ i a,
    t ≠ τ (x, i) + tagIncrement τ x a ∧ t ≠ τ (G.target.symm (x, i)) + tagIncrement τ x a
  let compatible (e : V × Fin d) (t u : Tag) := ∀ a b,
    t + u ≠ τ e + tagIncrement τ e.1 a + tagIncrement τ (G.target e).1 b
  have step (x : V) (f : V → Tag) :
      allowed x (G.chooseTag index τ hcard x f) ∧
      (∀ i, compatible (x, i) (G.chooseTag index τ hcard x f) (f (G.target (x, i)).1)) ∧
      (∀ i, compatible (G.target.symm (x, i)) (f (G.target.symm (x, i)).1)
        (G.chooseTag index τ hcard x f)) := by
    let t := G.chooseTag index τ hcard x f
    have ht (i : TagTests d) : t ≠ G.tagForbidden τ x f i := by
      intro hi
      exact (firstMissing (index ∘ G.tagForbidden τ x f)
        (by simpa [TagTests, pow_two] using hcard)).2 i
          (by simpa only [t, chooseTag, Equiv.apply_symm_apply, Function.comp_apply] using
            congrArg index hi)
    refine ⟨fun i a ↦ ⟨ht ((true, i), .inl a), ht ((false, i), .inl a)⟩, ?_, ?_⟩
    · intro i a b h
      exact ht ((true, i), .inr (a, b)) (eq_sub_iff_add_eq.mpr h)
    · intro i a b h
      apply ht ((false, i), .inr (a, b))
      apply eq_sub_iff_add_eq.mpr
      simpa only [Equiv.apply_symm_apply, add_comm t] using h
  obtain ⟨hu, he⟩ := G.scan_valid order 0 (G.chooseTag index τ hcard) allowed compatible step
  intro e
  refine ⟨fun a ↦ (hu e.1 e.2 a).1, ?_, he e⟩
  intro b
  simpa only [orderedTagOffsets, Prod.mk.eta, Equiv.symm_apply_apply] using
    (hu (G.target e).1 (G.target e).2 b).2

end SlotGraph

end Compression

end VPVNP
end Computability
end OAI
