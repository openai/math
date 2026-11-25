import OAI.Optimization.LinearProgramming.PriceGame.Computation
import OAI.Optimization.LinearProgramming.PriceGame.StatesOracle
import OAI.Optimization.LinearProgramming.PriceGame.Experts
import Mathlib.Data.List.FinRange

/-! Sequentially acquire all parent feedback using only designated root queries. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace States

variable {N R : ℕ} {anchor : Fin N} {J : Type}

/-- Read the supplied coordinate list in order. At a strict price change the value
is local. The program requests the designated label only at a tie. -/
def feedbackList (p : Path (Fin N) J) (y : J → ℚ) (x : J × Bool → ℚ)
    (coords : List J) : Computation N (List Bool) :=
  Computation.traverse (fun i => Computation.ofTree (feedbackAt p y x i)) coords

/-- Interpret an answer list as a coordinate vector. On the public coordinate
enumeration every entry is present; the default is used only outside that enumeration. -/
def lookupFeedback [DecidableEq J] : List J → List Bool → J → Bool
  | j :: js, b :: bs, i => if i = j then b else lookupFeedback js bs i
  | _, _, _ => false

private theorem lookupFeedback_of_forall₂ [DecidableEq J] (ok : J → Bool → Prop)
    {js : List J} {bs : List Bool} (all : List.Forall₂ ok js bs) {i : J} (hi : i ∈ js) :
    ok i (lookupFeedback js bs i) := by
  induction all with
  | nil => simp at hi
  | @cons j b js bs hhead _ ih =>
    by_cases he : i = j
    · subst j; simpa [lookupFeedback] using hhead
    · have hm := List.mem_cons.mp hi
      exact (by simpa [lookupFeedback, he] using ih (hm.resolve_left he))

def feedbackVector [DecidableEq J] (p : Path (Fin N) J) (y : J → ℚ) (x : J × Bool → ℚ)
    (coords : List J) : Computation N (J → Bool) :=
  (feedbackList p y x coords).map (lookupFeedback coords)

theorem feedbackAt_height_eq (p : Path (Fin N) J) (y : J → ℚ) (x : J × Bool → ℚ) (i : J) :
    (feedbackAt p y x i).height = if parentPrices y x i = y i then 1 else 0 := by
  by_cases h : parentPrices y x i = y i
  · simp [feedbackAt, h, readDesignated_height]
  · rcases lt_or_gt_of_ne h with hl | hl
    · simp [feedbackAt, hl, not_lt_of_gt hl, h, Tree.height]
    · simp [feedbackAt, hl, h, Tree.height]

/-- The feedback vector charges at most one root query for each tied coordinate.
Duplicate entries in the supplied enumeration are counted with multiplicity. -/
theorem feedbackVector_height [DecidableEq J] (p : Path (Fin N) J) (y : J → ℚ)
    (x : J × Bool → ℚ) (coords : List J) :
    (feedbackVector p y x coords).height ≤
      (coords.filter fun i => decide (parentPrices y x i = y i)).length := by
  rw [feedbackVector, Computation.height_map]
  have hb := Computation.height_traverse_le (fun i => Computation.ofTree (feedbackAt p y x i)) coords
  apply hb.trans
  clear hb
  induction coords with
  | nil => simp
  | cons i is ih =>
    have ht : (Computation.ofTree (feedbackAt p y x i)).height = (feedbackAt p y x i).height := by
      rw [← Computation.height_toTree, Computation.toTree_ofTree]
    simp only [List.map_cons, List.sum_cons, ht, feedbackAt_height_eq]
    by_cases he : parentPrices y x i = y i
    · simp [he]; omega
    · simpa [he] using ih

/-- A single public execution supplies simultaneous correct signs at every eligible,
active coordinate when the child succeeds. No compatibility between unforced answers
at different coordinates is required. -/
theorem feedbackVector_correct [DecidableEq J] (h : Hidden N R anchor) {p : Path (Fin N) J}
    {value y : J → ℚ} {active : J → Prop} {t t' : ℚ}
    (reached : Reachable h.positive (priority h) (· ∈ h.active) p value active t)
    (hshift : t ≤ t') (x : J × Bool → ℚ)
    (win : Succeeds (childActive active value y h.positive t') (fun q => value q.1)
      x h.positive t') (coords : List J) (v : J → Bool)
    (run : Computation.Reaches h (feedbackVector p y x coords) v) :
    ∀ i ∈ coords, active i → signed h.positive (y i) ≤ value i - t' → v i = h.positive := by
  obtain ⟨bs, hbs, rfl⟩ := (Computation.reaches_map_iff h _ _ _).mp run
  have hall := (Computation.reaches_traverse_iff h _ _ _).mp hbs
  intro i hi hai hei
  have hacq := lookupFeedback_of_forall₂ _ hall hi
  have hreach := (Computation.reaches_toTree_iff h _ _).mpr hacq
  rw [Computation.toTree_ofTree] at hreach
  exact feedbackAt_correct h reached hshift x win i hai hei _ hreach

private def duplicateVertices {α : Type*} (xs : List α) : List (α × Bool) :=
  xs.flatMap fun i => [(i, false), (i, true)]

/-- Enumerate vertices in the public binary duplication order. -/
def allVertices (N : ℕ) : (l : ℕ) → List (Mass.Vertex N l)
  | 0 => List.finRange N
  | l + 1 => duplicateVertices (allVertices N l)

theorem mem_allVertices (N l : ℕ) (i : Mass.Vertex N l) : i ∈ allVertices N l := by
  induction l with
  | zero => exact List.mem_finRange i
  | succ l ih =>
    obtain ⟨i, b⟩ := i
    change (i, b) ∈ duplicateVertices (allVertices N l)
    apply List.mem_flatMap.mpr
    exact ⟨i, ih i, by cases b <;> simp⟩

private theorem duplicate_length {α : Type*} (xs : List α) :
    (duplicateVertices xs).length = 2 * xs.length := by
  unfold duplicateVertices
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons, ih]
    omega

theorem length_allVertices (N l : ℕ) : (allVertices N l).length = Fintype.card (Mass.Vertex N l) := by
  induction l with
  | zero =>
    rw [Mass.card_vertices, pow_zero, one_mul]
    exact List.length_finRange
  | succ l ih =>
    change (duplicateVertices (allVertices N l)).length = _
    rw [duplicate_length, ih, Mass.card_vertices, Mass.card_vertices, pow_succ]
    ac_rfl

/-- The complete feedback obtained by the probe stage of a recursive trial. -/
def feedbackAll {N l : ℕ} (p : Path (Fin N) (Mass.Vertex N l))
    (y : Mass.Vertex N l → ℚ) (x : Mass.Vertex N (l + 1) → ℚ) :
    Computation N (Mass.Vertex N l → Bool) :=
  feedbackVector p y x (allVertices N l)

theorem feedbackAll_height {N l : ℕ} (p : Path (Fin N) (Mass.Vertex N l))
    (y : Mass.Vertex N l → ℚ) (x : Mass.Vertex N (l + 1) → ℚ) :
    (feedbackAll p y x).height ≤ Fintype.card (Mass.Vertex N l) := by
  unfold feedbackAll
  exact (feedbackVector_height _ _ _ _).trans ((List.length_filter_le ..).trans (length_allVertices N l).le)

theorem feedbackAll_correct {l : ℕ} (h : Hidden N R anchor) {p : Path (Fin N) (Mass.Vertex N l)}
    {value y : Mass.Vertex N l → ℚ} {active : Mass.Vertex N l → Prop} {t t' : ℚ}
    (reached : Reachable h.positive (priority h) (· ∈ h.active) p value active t)
    (hshift : t ≤ t') (x : Mass.Vertex N (l+1) → ℚ)
    (win : Succeeds (childActive active value y h.positive t') (fun q => value q.1)
      x h.positive t') (v : Mass.Vertex N l → Bool)
    (run : Computation.Reaches h (feedbackAll p y x) v) :
    ∀ i, active i → signed h.positive (y i) ≤ value i - t' → v i = h.positive :=
  fun i => feedbackVector_correct h reached hshift x win _ v run i (mem_allVertices _ _ _)

end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
