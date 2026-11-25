import OAI.LinearAlgebra.SpectralBooks.DepthLimit
import Mathlib.Data.List.FinRange

/-! # Cycling the marked indices in a relocation tree

In each round of the many-index relocation argument all marked coordinates are
split once. The ideal table and its threshold at a node depend on its finite
branch history. Thus the finitely many wire-ratio estimates needed for a fixed
schedule can be made simultaneous before selecting an actual branch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter

namespace ManyRelocation

/-- A fixed order of marks, repeated once per round. -/
def rounds (r : ℕ) : ℕ → List (Fin r)
  | 0 => []
  | n + 1 => List.finRange r ++ rounds r n

@[simp] theorem count_rounds {r : ℕ} (j : Fin r) (n : ℕ) : (rounds r n).count j = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rounds, ih, Nat.add_comm]

@[simp] theorem length_rounds (r n : ℕ) : (rounds r n).length = r * n := by
  induction n with
  | zero => simp [rounds]
  | succ n ih => simp [rounds, ih, Nat.mul_succ, Nat.add_comm]

variable {ι T : Type*} (child : T → ι → Bool → T)

/-- The leaf tables reached after splitting a specified list of coordinates. -/
def Reaches : List ι → T → T → Prop
  | [], N, M => N = M
  | i :: rest, N, M => ∃ b, Reaches rest (child N i b) M

/-- A side condition holds at every internal node of the prescribed finite tree. -/
def AtEveryNode (ok : T → ι → Prop) : List ι → T → Prop
  | [], _ => True
  | i :: rest, N => ok N i ∧ ∀ b, AtEveryNode ok rest (child N i b)

/-- All internal nodes can use the same sufficiently large tensor power, even
when their individual dimension thresholds depend on the history of splits. -/
theorem eventually_atEveryNode {I : Type*} {l : Filter I} (ok : I → T → ι → Prop)
    (inv : T → Prop) (pres : ∀ N i b, inv N → inv (child N i b))
    (h : ∀ N i, inv N → ∀ᶠ n in l, ok n N i) (sites : List ι) (N : T) (hN : inv N) :
    ∀ᶠ n in l, AtEveryNode child (ok n) sites N := by
  induction sites generalizing N with
  | nil => exact .of_forall fun _ => trivial
  | cons i rest ih =>
    filter_upwards [h N i hN, ih (child N i false) (pres N i false hN),
        ih (child N i true) (pres N i true hN)] with n hroot hleft hright
    exact ⟨hroot, fun b => by cases b <;> assumption⟩

/-- Each split halves the range on its own coordinate and never increases the
range along other coordinates. -/
theorem width_at_leaf [DecidableEq ι] (width : T → ι → ℝ)
    (hsplit : ∀ N i b, width (child N i b) i ≤ width N i / 2)
    (hother : ∀ N i j b, j ≠ i → width (child N i b) j ≤ width N j)
    {sites : List ι} {N M : T} (h : Reaches child sites N M) (j : ι) :
    width M j ≤ width N j / 2 ^ sites.count j := by
  induction sites generalizing N with
  | nil => cases h; simp
  | cons i rest ih =>
    obtain ⟨b, h⟩ := h
    refine (ih h).trans ?_
    by_cases hij : j = i
    · subst j
      simp only [List.count_cons_self, pow_succ]
      rw [mul_comm ((2 : ℝ) ^ _), ← div_div]
      exact div_le_div_of_nonneg_right (hsplit N i b) (by positivity)
    · simp only [List.count_cons_of_ne (Ne.symm hij)]
      exact div_le_div_of_nonneg_right (hother N i j b hij) (by positivity)

theorem le_of_reaches [Preorder T] (parent : ∀ N i b, child N i b ≤ N)
    {sites : List ι} {N M : T} (h : Reaches child sites N M) : M ≤ N := by
  induction sites generalizing N with
  | nil => cases h; rfl
  | cons i rest ih =>
    obtain ⟨b, hb⟩ := h
    exact (ih hb).trans (parent N i b)

/-- Select a surviving actual tensor at every split. The error in the lower
bound on the interior value and the upper bound on endpoint values both grow
by at most one step tolerance per level. -/
theorem selectedLeaf {X : Type*} (inside : X → ℝ) (bounded : X → T → ℝ → Prop)
    (ok : T → ι → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (step : ∀ x N i σ, ok N i → 0 ≤ σ → bounded x N σ →
      ∃ y b, inside x ≤ inside y + ε ∧ bounded y (child N i b) (σ + ε))
    (sites : List ι) (N : T) (x : X) {σ : ℝ} (hσ : 0 ≤ σ) (hx : bounded x N σ)
    (hcheck : AtEveryNode child ok sites N) :
    ∃ y M, Reaches child sites N M ∧ inside x ≤ inside y + sites.length * ε ∧
      bounded y M (σ + sites.length * ε) := by
  induction sites generalizing N x σ with
  | nil => exact ⟨x, N, rfl, by simp, by simpa using hx⟩
  | cons i rest ih =>
    obtain ⟨y, b, hxy, hy⟩ := step x N i σ hcheck.1 hσ hx
    obtain ⟨z, M, hpath, hyz, hz⟩ := ih (child N i b) y (add_nonneg hσ hε) hy (hcheck.2 b)
    refine ⟨z, M, ⟨b, hpath⟩, ?_, ?_⟩
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
    · convert hz using 1
      simp [add_mul]
      ring

end ManyRelocation

end SpectralBooks
end LinearAlgebra
end OAI
