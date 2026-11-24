import OAI.Computability.VPVNP.TensorPowerCNF

/-! # An exact-one incidence matrix for tensor powers

One block of columns selects a word at each party. Another block selects a
tuple of digits at each position. Each consistency row counts a true bit on the
word side and a false bit on the tuple side, so exact-one means the bits agree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TensorPowerCNF

open MvPolynomial
open scoped Classical

/-- Columns carrying the word and tuple selection flags. -/
abbrev Col (J : Type*) (b h : ℕ) := (J × Word b h) ⊕ (Fin h × (J → Digit b))

/-- A row for each one-hot field and each bit agreement. -/
abbrev Row (J : Type*) (b h : ℕ) := (J ⊕ Fin h) ⊕ (J × (Fin h × Fin b))

theorem card_col (J : Type*) [Fintype J] (b h : ℕ) :
    Fintype.card (Col J b h) = Fintype.card J * (2 ^ b) ^ h + h * (2 ^ b) ^ Fintype.card J := by
  simp [Col, Word, Digit]

theorem card_row (J : Type*) [Fintype J] (b h : ℕ) :
    Fintype.card (Row J b h) = Fintype.card J + h + Fintype.card J * (h * b) := by
  simp [Row]

variable {J : Type*} {b h : ℕ}

/-- The entries for word and tuple columns use opposite polarities on a bit row. -/
noncomputable def incidence : Row J b h → Col J b h → Bool
  | .inl (.inl j), .inl (j', _) => decide (j = j')
  | .inl (.inr t), .inr (t', _) => decide (t = t')
  | .inl _, _ => false
  | .inr (j, t, a), .inl (j', w) => decide (j = j') && w t a
  | .inr (j, t, a), .inr (t', u) => decide (t = t') && !(u j a)

/-- A selected word contributes a variable, and a selected tuple contributes a tensor entry. -/
def columnWeight {R : Type*} (T : (J → Digit b) → R) (h : ℕ) :
    Col J b h → (J × Word b h) ⊕ R
  | .inl jw => .inl jw
  | .inr (_, u) => .inr (T u)

private noncomputable def flags (p : J → Word b h) (q : Fin h → J → Digit b) :
    Col J b h → Bool
  | .inl (j, w) => decide (p j = w)
  | .inr (t, u) => decide (q t = u)

private def Exact (x : Col J b h → Bool) : Prop :=
  ∀ r : Row J b h, ∃! i, x i = true ∧ incidence r i = true

private theorem wordRow_iff (x : Col J b h → Bool) (j : J) :
    (∃! i, x i = true ∧ incidence (.inl (.inl j)) i = true) ↔
      ∃! w, x (.inl (j, w)) = true := by
  simp [ExistsUnique, Sum.exists, Sum.forall, Prod.exists, Prod.forall, incidence]
  grind

private theorem tupleRow_iff (x : Col J b h → Bool) (t : Fin h) :
    (∃! i, x i = true ∧ incidence (.inl (.inr t)) i = true) ↔
      ∃! u, x (.inr (t, u)) = true := by
  simp [ExistsUnique, Sum.exists, Sum.forall, Prod.exists, Prod.forall, incidence]
  grind

private theorem bitRow_iff (p : J → Word b h) (q : Fin h → J → Digit b)
    (j : J) (t : Fin h) (a : Fin b) :
    (∃! i, flags p q i = true ∧ incidence (.inr (j, t, a)) i = true) ↔ p j t a = q t j a := by
  have hx (i : Col J b h) :
      (flags p q i = true ∧ incidence (.inr (j, t, a)) i = true) ↔
        (i = .inl (j, p j) ∧ p j t a = true) ∨ (i = .inr (t, q t) ∧ q t j a = false) := by
    rcases i with ⟨j', w⟩ | ⟨t', u⟩
    · simp [incidence, flags]
      aesop
    · simp [incidence, flags]
      aesop
  simp_rw [hx]
  cases hp : p j t a <;> cases hq : q t j a <;>
    simp [ExistsUnique]

private noncomputable def selection (p : J → Word b h) : Col J b h → Bool :=
  flags p (fun t j => p j t)

private theorem exact_selection (p : J → Word b h) : Exact (selection p) := by
  rintro ((j | t) | ⟨j, t, a⟩)
  · rw [wordRow_iff]
    simp [selection, flags, ExistsUnique]
  · rw [tupleRow_iff]
    simp [selection, flags, ExistsUnique]
  · exact (bitRow_iff p _ j t a).mpr rfl

private theorem exists_selection (x : Col J b h → Bool) (hx : Exact x) :
    ∃ p : J → Word b h, selection p = x := by
  choose p hp hp' using fun j => (wordRow_iff x j).mp (hx (.inl (.inl j)))
  choose q hq hq' using fun t => (tupleRow_iff x t).mp (hx (.inl (.inr t)))
  have he : flags p q = x := by
    funext i
    apply Bool.eq_iff_iff.mpr
    rcases i with ⟨j, w⟩ | ⟨t, u⟩
    · simp only [flags, decide_eq_true_eq]
      exact ⟨fun e => e ▸ hp j, fun hw => (hp' j w hw).symm⟩
    · simp only [flags, decide_eq_true_eq]
      exact ⟨fun e => e ▸ hq t, fun hu => (hq' t u hu).symm⟩
  have hbits : (fun t j => p j t) = q := by
    funext t j a
    apply (bitRow_iff p q j t a).mp
    rw [he]
    exact hx (.inr (j, t, a))
  exact ⟨p, by simpa only [selection, hbits] using he⟩

private noncomputable def exactSelectionEquiv :
    (J → Word b h) ≃ {x : Col J b h → Bool // Exact x} :=
  Equiv.ofBijective (fun p => ⟨selection p, exact_selection p⟩) (by
    constructor
    · intro p p' he
      have he' := congrArg Subtype.val he
      funext j
      have hc := congrFun he' (.inl (j, p' j))
      simpa [selection, flags] using hc
    · intro x
      obtain ⟨p, hp⟩ := exists_selection x.val x.property
      exact ⟨p, Subtype.ext hp⟩)

variable [Fintype J] {R : Type*} [CommSemiring R]

private theorem selectedWeight (T : (J → Digit b) → R) (p : J → Word b h) :
    (∏ i, if selection p i then (columnWeight T h i).elim X C else 1) =
      (∏ j, X (j, p j)) * ∏ t, C (T (fun j => p j t)) := by
  simp [Fintype.prod_sum_type, Fintype.prod_prod_type, selection, flags, columnWeight]

/-- Summing the weights of all exact-one solutions gives the regrouped tensor power form. -/
theorem weightedIncidence_eq_form (T : (J → Digit b) → R) (h : ℕ) :
    (∑ x : Col J b h → Bool,
      if ∀ r : Row J b h, ∃! i, x i = true ∧ incidence r i = true then
        ∏ i, if x i then (columnWeight T h i).elim X C else 1 else 0) = form T h := by
  let w (x : Col J b h → Bool) := ∏ i, if x i then (columnWeight T h i).elim X C else 1
  have hs : (∑ x : Col J b h → Bool,
      if ∀ r : Row J b h, ∃! i, x i = true ∧ incidence r i = true then w x else 0) =
      ∑ x : {v // Exact v}, w x.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun x => by simp [Exact]) _
  rw [hs, ← exactSelectionEquiv.sum_comp, form]
  exact Finset.sum_congr rfl (fun p _ => selectedWeight T p)

end TensorPowerCNF

end VPVNP
end Computability
end OAI
