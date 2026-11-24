import OAI.Computability.VPVNP.DegreeRefreshWidths
import Mathlib.Data.Fintype.BigOperators

/-!
# Shared payloads of the refreshed graph

The summation over the actual arcs in (7.1) is equivalent to choosing the
external strings and a separate internal expander assignment in each block.
Every padding arc carries the unique string of length zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

namespace Compression.Refresh

variable {V L : Type*} {D dH d₀ : ℕ}

/-- A refreshed outgoing arc consists of a base port, a remaining lane, and
one of the new degree-`d₀` slots. -/
abbrev ActualArc (V L : Type*) (D d₀ : ℕ) := ((V × Fin D) × L) × Fin d₀

/-- Read the block, its port, and the class of the numbered slot. -/
def arcCoordinates (hd : dH + 1 ≤ d₀) :
    ActualArc V L D d₀ ≃ ((V × L) × Fin D) × RefreshSlot dH d₀ where
  toFun a := (((a.1.1.1,a.1.2),a.1.1.2), (refreshSlots hd).symm a.2)
  invFun q := (((q.1.1.1,q.1.2),q.1.1.2), refreshSlots hd q.2)
  left_inv _ := by simp
  right_inv _ := by simp

variable (ext : (V × L) × Fin D → ℕ) (internal : V × L → Fin D × Fin dH → ℕ)

private def classWidth (a : ((V × L) × Fin D) × RefreshSlot dH d₀) : ℕ :=
  match a.2 with
  | .inl _ => ext a.1
  | .inr (.inl h) => internal a.1.1 (a.1.2,h)
  | .inr (.inr _) => 0

/-- Width on the actual outgoing arc index of `degreeRefresh`. -/
def actualWidth (hd : dH + 1 ≤ d₀) (ext : (V × L) × Fin D → ℕ)
    (internal : V × L → Fin D × Fin dH → ℕ) (a : ActualArc V L D d₀) : ℕ :=
  classWidth ext internal (arcCoordinates hd a)

private def classPayloads :
    ((a : ((V × L) × Fin D) × RefreshSlot dH d₀) → Fin (classWidth ext internal a) → Bool) ≃
      ((b : (V × L) × Fin D) → Fin (ext b) → Bool) ×
        ((s : V × L) → (e : Fin D × Fin dH) → Fin (internal s e) → Bool) where
  toFun f := (fun b => f (b,.inl 0), fun s e => f ((s,e.1),.inr (.inl e.2)))
  invFun p a := match a with
    | (b, .inl _) => p.1 b
    | ((s,j), .inr (.inl h)) => p.2 s (j,h)
    | (_, .inr (.inr _)) => Fin.elim0
  left_inv f := by
    funext a
    rcases a with ⟨b, k | k | k⟩
    · cases Subsingleton.elim k 0
      rfl
    · rfl
    · funext i
      exact Fin.elim0 i
  right_inv _ := rfl

/-- Shared actual-arc payloads are exactly one external assignment and one
internal assignment per block. Empty padding payloads add no summation index. -/
def payloadsEquiv (hd : dH + 1 ≤ d₀) (ext : (V × L) × Fin D → ℕ)
    (internal : V × L → Fin D × Fin dH → ℕ) :
    ((a : ActualArc V L D d₀) → Fin (actualWidth hd ext internal a) → Bool) ≃
      ((b : (V × L) × Fin D) → Fin (ext b) → Bool) ×
        ((s : V × L) → (e : Fin D × Fin dH) → Fin (internal s e) → Bool) :=
  (Equiv.piCongrLeft (fun a => Fin (classWidth ext internal a) → Bool) (arcCoordinates hd)).trans
    (classPayloads ext internal)

/-- This actual-arc width specializes to the width charged in (7.3). -/
theorem actualWidth_eq_newWidths (hd : dH + 1 ≤ d₀) (w : DegreeRefresh.Widths (V × L) D)
    (a : ActualArc V L D d₀) :
    actualWidth hd (fun b => ∑ j, w b j) internal a =
      DegreeRefresh.newWidths hd w internal ((a.1.1.1,a.1.2),a.1.1.2) a.2 := rfl

@[simp] theorem actualWidth_external (hd : dH + 1 ≤ d₀) (b : (V × L) × Fin D) :
    actualWidth hd ext internal (((b.1.1,b.2),b.1.2),refreshSlots hd (.inl 0)) = ext b := by
  simp [actualWidth, arcCoordinates, classWidth]

@[simp] theorem actualWidth_internal (hd : dH + 1 ≤ d₀) (s : V × L) (e : Fin D × Fin dH) :
    actualWidth hd ext internal (((s.1,e.1),s.2),refreshSlots hd (.inr (.inl e.2))) =
      internal s e := by
  simp [actualWidth, arcCoordinates, classWidth]

/-- Read the external component at its numbered actual slot. -/
theorem payloadsEquiv_external (hd : dH + 1 ≤ d₀)
    (f : (a : ActualArc V L D d₀) → Fin (actualWidth hd ext internal a) → Bool)
    (b : (V × L) × Fin D) :
    (payloadsEquiv hd ext internal f).1 b =
      cast (congrArg (fun n => Fin n → Bool) (actualWidth_external ext internal hd b))
        (f (((b.1.1,b.2),b.1.2),refreshSlots hd (.inl 0))) :=
  Equiv.piCongrLeft_apply_eq_cast (P := fun a => Fin (classWidth ext internal a) → Bool)
    (e := arcCoordinates hd) f (b,.inl 0)

/-- Read a block's internal component at its numbered expander slot. -/
theorem payloadsEquiv_internal (hd : dH + 1 ≤ d₀)
    (f : (a : ActualArc V L D d₀) → Fin (actualWidth hd ext internal a) → Bool)
    (s : V × L) (e : Fin D × Fin dH) :
    (payloadsEquiv hd ext internal f).2 s e =
      cast (congrArg (fun n => Fin n → Bool) (actualWidth_internal ext internal hd s e))
        (f (((s.1,e.1),s.2),refreshSlots hd (.inr (.inl e.2)))) :=
  Equiv.piCongrLeft_apply_eq_cast (P := fun a => Fin (classWidth ext internal a) → Bool)
    (e := arcCoordinates hd) f ((s,e.1),.inr (.inl e.2))

/-- The equality of finite sums used to replace the separate external and
internal choices by the single shared arc assignment of (7.1). -/
theorem sum_payloads [Fintype V] [Fintype L] (hd : dH + 1 ≤ d₀) {A : Type*} [AddCommMonoid A]
    (f : ((b : (V × L) × Fin D) → Fin (ext b) → Bool) →
      ((s : V × L) → (e : Fin D × Fin dH) → Fin (internal s e) → Bool) → A) :
    (∑ a, f ((payloadsEquiv hd ext internal a).1) ((payloadsEquiv hd ext internal a).2)) =
      ∑ x, ∑ y, f x y := by
  classical
  rw [← Fintype.sum_prod_type']
  exact (payloadsEquiv hd ext internal).sum_comp (fun p => f p.1 p.2)

end Compression.Refresh

end VPVNP
end Computability
end OAI
