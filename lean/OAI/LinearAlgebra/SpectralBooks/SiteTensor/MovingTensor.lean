import OAI.LinearAlgebra.SpectralBooks.MarkedRelocation
import OAI.LinearAlgebra.SpectralBooks.Prices

/-! # Fixed movable indices in an exterior splitting tree

Each mark occupies one tensor index. Every other index has a fixed placement.
Splitting one marked index creates a new copy of that mark and two fixed
exterior indices. The other marks keep their original coordinate dimensions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace SiteTensor.Relocation

/-- A tensor with `r` movable indices of prescribed dimensions and any number of
fixed auxiliary indices. The total index type may change at each exterior split. -/
structure MovingTensor (J : Type) (K : Type*) {r : ℕ} (q : Fin r → ℕ) where
  I : Type
  finiteI : Fintype I
  T : Raw.{0} I K
  mark : Fin r → I
  slot : I → Fin r ⊕ J
  slot_mark : ∀ i, slot (mark i) = .inl i
  eq_mark : ∀ k i, slot k = .inl i → k = mark i
  markEquiv : ∀ i, T.Leg (mark i) ≃ Fin (q i)

attribute [instance] MovingTensor.finiteI

namespace MovingTensor

variable {r : ℕ} {q : Fin r → ℕ} {J : Type} {K : Type*}

/-- Begin with the given movable raw tensor and no auxiliary indices. -/
def ofRaw (T : Raw.{0} (Fin r) K) (e : ∀ i, T.Leg i ≃ Fin (q i)) : MovingTensor J K q where
  I := Fin r
  finiteI := inferInstance
  T := T
  mark := id
  slot := Sum.inl
  slot_mark _ := rfl
  eq_mark _ _ h := Sum.inl.inj h
  markEquiv := e

/-- The root for an `n`th tensor power. Its moving dimensions are the powers
of the original dimensions. -/
def ofPower [Field K] (T : Raw.{0} (Fin r) K) (n : ℕ) :
    MovingTensor J K (fun i ↦ Fintype.card (T.Leg i) ^ n) :=
  ofRaw (T.powerTensor n) fun i ↦ Fintype.equivFinOfCardEq (by
    change Fintype.card (Fin n → T.Leg i) = _
    simp)

variable (s : MovingTensor J K q)

theorem mark_injective : Function.Injective s.mark := by
  intro i j hij
  exact Sum.inl.inj ((s.slot_mark i).symm.trans ((congrArg s.slot hij).trans (s.slot_mark j)))

/-- Fill the movable slots of a state with their new sites. -/
def placement (p : Fin r → J) (k : s.I) : J := (s.slot k).elim p id

@[simp] theorem placement_mark (p : Fin r → J) (i : Fin r) : s.placement p (s.mark i) = p i := by
  simp [placement, s.slot_mark]

/-- Tensor evaluated at a movable placement, including all fixed auxiliary sites. -/
def grouped (p : Fin r → J) : Raw.{0} J K := s.T.group (s.placement p)

@[simp] theorem ofRaw_grouped (T : Raw.{0} (Fin r) K) (e : ∀ i, T.Leg i ≃ Fin (q i))
    (p : Fin r → J) : (ofRaw T e).grouped p = T.group p := rfl

@[simp] theorem ofPower_grouped [Field K] (T : Raw.{0} (Fin r) K) (n : ℕ)
    (p : Fin r → J) : (ofPower T n).grouped p = (T.powerTensor n).group p := rfl

/-- Placement of all indices except the particular mark being split. -/
def background (i : Fin r) (p : Fin r → J) : {k // k ≠ s.mark i} → J :=
  s.placement p ∘ Subtype.val

@[simp] theorem background_update_same (i : Fin r) (p : Fin r → J) (a : J) :
    s.background i (Function.update p i a) = s.background i p := by
  funext k
  change (s.slot k.val).elim _ _ = (s.slot k.val).elim _ _
  cases hs : s.slot k.val with
  | inl j =>
    have hji : j ≠ i := fun heq ↦ k.property (s.eq_mark k.val i (heq ▸ hs))
    exact Function.update_of_ne hji _ _
  | inr _ => rfl

/-- Basis family at the complementary indices of a marked split. -/
abbrev backgroundLeg (i : Fin r) (k : {k // k ≠ s.mark i}) := s.T.Leg k.val

/-- Original coefficients with the chosen mark separated and labeled by its
fixed set of indices `Fin (q i)`. -/
def markedCoeff (i : Fin r) (x : ∀ k, s.backgroundLeg i k) (t : Fin (q i)) : K :=
  markCoeff s.T (s.mark i) x ((s.markEquiv i).symm t)

/-- Splitting off the marked index preserves the grouped restriction class. -/
theorem ofRaw_grouped_eq_marked [Fintype J] [Field K] (i : Fin r) (p : Fin r → J) :
    SiteTensor.ofRaw (s.grouped p) =
      SiteTensor.ofRaw ((marked (s.backgroundLeg i) (Fin (q i)) (s.markedCoeff i)).group
        (placeMark (s.background i p) (p i))) := by
  rw [← s.placement_mark p i]
  exact ofRaw_group_eq_markFin s.T (s.mark i) (s.markEquiv i) (s.placement p)

/-- Nonzero states stay nonzero when the distinguished index is pulled out. -/
theorem marked_ne_zero [Field K] (i : Fin r) (hs : s.T.coeff ≠ 0) :
    (marked (s.backgroundLeg i) (Fin (q i)) (s.markedCoeff i)).coeff ≠ 0 :=
  marked_fin_ne_zero s.T (s.mark i) (s.markEquiv i) hs

private def childMark (i j : Fin r) : {k // k ≠ s.mark i} ⊕ Fin 3 :=
  if h : j = i then .inr 0 else .inl ⟨s.mark j, fun hk ↦ h (s.mark_injective hk)⟩

private def childSlot (i : Fin r) (a b : J) : {k // k ≠ s.mark i} ⊕ Fin 3 → Fin r ⊕ J :=
  Sum.elim (s.slot ∘ Subtype.val) ![Sum.inl i, Sum.inr a, Sum.inr b]

/-- Make a new state from either exterior factorization. The first new index is
the replacement mark and the column and row remain at fixed sites `a` and `b`. -/
def child (i : Fin r) (H : Type) [Fintype H] (a b : J)
    (S : (∀ k, s.backgroundLeg i k) → Fin (q i) → H → H → K) : MovingTensor J K q where
  I := {k // k ≠ s.mark i} ⊕ Fin 3
  finiteI := inferInstance
  T := split (s.backgroundLeg i) (Fin (q i)) H S
  mark := s.childMark i
  slot := s.childSlot i a b
  slot_mark j := by
    by_cases h : j = i
    · subst j
      simp [childMark, childSlot]
    · simp [childMark, childSlot, h, s.slot_mark]
  eq_mark k j hk := by
    rcases k with k | k
    · change s.slot k.val = .inl j at hk
      have heq := s.eq_mark k.val j hk
      have hji : j ≠ i := fun h ↦ k.property (heq.trans (congrArg s.mark h))
      simp only [childMark, dite_eq_right hji, Sum.inl.injEq]
      exact Subtype.ext heq
    · fin_cases k <;> simp [childSlot] at hk
      subst j
      simp [childMark]
  markEquiv j := by
    by_cases h : j = i
    · subst j
      simp only [childMark]
      exact Equiv.refl _
    · simp only [childMark, dite_eq_right h]
      exact s.markEquiv j

/-- Evaluation of a child is precisely evaluation of the exterior split at its
moving mark and its two fixed exterior sites, for every placement of every mark. -/
theorem grouped_child (i : Fin r) (H : Type) [Fintype H] (a b : J)
    (S : (∀ k, s.backgroundLeg i k) → Fin (q i) → H → H → K) (p : Fin r → J) :
    (s.child i H a b S).grouped p =
      (split (s.backgroundLeg i) (Fin (q i)) H S).group (placeSplit (s.background i p) (p i) a b) := by
  apply congrArg ((split (s.backgroundLeg i) (Fin (q i)) H S).group)
  funext k
  rcases k with _ | k
  · rfl
  · fin_cases k <;> rfl

end MovingTensor
end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
