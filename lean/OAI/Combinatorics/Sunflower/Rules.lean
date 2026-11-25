import OAI.Combinatorics.Sunflower.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype

/-! # The two-anchor implication system -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {G I α : Type*}

/-- Equality of the symbols on the two antecedents obliges the target to agree. -/
structure Rule (G : Type*) where
  left : G
  right : G
  target : G
  deriving DecidableEq, Fintype

def Rule.Holds (q : Rule G) (f : G → α) : Prop :=
  f q.left = f q.right → f q.left = f q.target

theorem Rule.not_holds_iff (q : Rule G) (f : G → α) :
    ¬ q.Holds f ↔ f q.left = f q.right ∧ f q.left ≠ f q.target := by
  classical
  simp [Rule.Holds]

/-- In the fourth rule each unordered pair of satellites occurs once. -/
inductive IsAnchorRule [LT G] (A B : G) : Rule G → Prop where
  | anchors (i : G) (hiA : i ≠ A) (hiB : i ≠ B) :
      IsAnchorRule A B ⟨A, B, i⟩
  | left (i : G) (hiA : i ≠ A) (hiB : i ≠ B) :
      IsAnchorRule A B ⟨A, i, B⟩
  | right (i : G) (hiA : i ≠ A) (hiB : i ≠ B) :
      IsAnchorRule A B ⟨B, i, A⟩
  | satellites (i j : G) (hiA : i ≠ A) (hiB : i ≠ B) (hjA : j ≠ A) (hjB : j ≠ B)
      (hij : i < j) : IsAnchorRule A B ⟨i, j, A⟩

theorem IsAnchorRule.distinct [Preorder G] {A B : G} {q : Rule G}
    (hq : IsAnchorRule A B q) (hAB : A ≠ B) :
    q.left ≠ q.right ∧ q.left ≠ q.target ∧ q.right ≠ q.target := by
  cases hq with
  | anchors i hiA hiB => exact ⟨hAB, hiA.symm, hiB.symm⟩
  | left i hiA hiB => exact ⟨hiA.symm, hAB, hiB⟩
  | right i hiA hiB => exact ⟨hiB.symm, hAB.symm, hiA⟩
  | satellites i j hiA _ hjA _ hij => exact ⟨ne_of_lt hij, hiA, hjA⟩

noncomputable def anchorRules [Fintype G] [LT G] (A B : G) : Finset (Rule G) := by
  classical
  exact Finset.univ.filter (IsAnchorRule A B)

@[simp] theorem mem_anchorRules [Fintype G] [LT G] {A B : G} {q : Rule G} :
    q ∈ anchorRules A B ↔ IsAnchorRule A B q := by
  classical
  simp [anchorRules]

/-- With groups numbered by `Fin (n+2)`, the four geometric constructions
suffice to discharge a property of every rule. -/
theorem anchorRules_fin_cases {n : ℕ} {P : Rule (Fin (n + 2)) → Prop}
    (ab : ∀ i : Fin n, P ⟨0, 1, i.succ.succ⟩)
    (az : ∀ i : Fin n, P ⟨0, i.succ.succ, 1⟩)
    (bz : ∀ i : Fin n, P ⟨1, i.succ.succ, 0⟩)
    (zz : ∀ i j : Fin n, i < j → P ⟨i.succ.succ, j.succ.succ, 0⟩)
    {q : Rule (Fin (n + 2))} (hq : q ∈ anchorRules 0 1) : P q := by
  have satellite (i : Fin (n + 2)) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
      ∃ j : Fin n, j.succ.succ = i := by
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
    have hj : j ≠ 0 := fun h => hi1 (h ▸ Fin.succ_zero_eq_one)
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
    exact ⟨j', rfl⟩
  cases mem_anchorRules.mp hq with
  | anchors i hiA hiB =>
    obtain ⟨i, rfl⟩ := satellite i hiA hiB
    exact ab i
  | left i hiA hiB =>
    obtain ⟨i, rfl⟩ := satellite i hiA hiB
    exact az i
  | right i hiA hiB =>
    obtain ⟨i, rfl⟩ := satellite i hiA hiB
    exact bz i
  | satellites i j hiA hiB hjA hjB hij =>
    obtain ⟨i, rfl⟩ := satellite i hiA hiB
    obtain ⟨j, rfl⟩ := satellite j hjA hjB
    exact zz i j (by simpa using hij)

/-- For unequal anchor symbols, every remaining group has a symbol different from either
anchor, and the satellite-pair rules make these remaining symbols pairwise different. -/
theorem admissible_of_isAnchorRule [LinearOrder G] {A B : G} (f : G → α)
    (hr : ∀ q, IsAnchorRule A B q → q.Holds f) : Admissible f := by
  classical
  by_cases hab : f A = f B
  · left
    have hall (i : G) : f A = f i := by
      by_cases hiA : i = A
      · rw [hiA]
      by_cases hiB : i = B
      · simpa only [hiB] using hab
      exact hr _ (.anchors i hiA hiB) hab
    exact fun i j => (hall i).symm.trans (hall j)
  · right
    have left_ne {i : G} (hiA : i ≠ A) : f A ≠ f i := by
      by_cases hiB : i = B
      · simpa only [hiB] using hab
      exact fun h => hab (hr _ (.left i hiA hiB) h)
    have right_ne {i : G} (hiB : i ≠ B) : f B ≠ f i := by
      by_cases hiA : i = A
      · simpa only [hiA] using (Ne.symm hab)
      exact fun h => hab (hr _ (.right i hiA hiB) h).symm
    intro i j hij
    by_contra hne
    by_cases hiA : i = A
    · subst i
      exact left_ne (Ne.symm hne) hij
    by_cases hjA : j = A
    · subst j
      exact left_ne hne hij.symm
    by_cases hiB : i = B
    · subst i
      exact right_ne (Ne.symm hne) hij
    by_cases hjB : j = B
    · subst j
      exact right_ne hne hij.symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact left_ne hiA (hr _ (.satellites i j hiA hiB hjA hjB hlt) hij).symm
    · exact left_ne hjA (hr _ (.satellites j i hjA hjB hiA hiB hgt) hij.symm).symm

theorem admissible_of_anchorRules [Fintype G] [LinearOrder G] {A B : G} (_hAB : A ≠ B)
    (f : G → α) (h : ∀ q ∈ anchorRules A B, q.Holds f) : Admissible f :=
  admissible_of_isAnchorRule f fun q hq => h q (mem_anchorRules.mpr hq)

/-- A nonconstant assignment of words from a free family must violate some rule at some
coordinate. This gives the zero factor in the expansion of the controlled restriction. -/
theorem exists_violated_anchorRule {r : ℕ} {W : Finset (I → α)} (hfree : WordFree r W)
    {A B : Fin r} (hAB : A ≠ B) (w : Fin r → I → α) (hmem : ∀ i, w i ∈ W)
    (h : ¬ IsConstant w) :
    ∃ c q, q ∈ anchorRules A B ∧ ¬ q.Holds (fun i => w i c) := by
  classical
  by_contra hn
  apply h
  apply hfree w hmem
  intro c
  apply admissible_of_anchorRules hAB
  intro q hq
  by_contra hv
  exact hn ⟨c, q, hq, hv⟩

end Sunflower
end Combinatorics
end OAI
