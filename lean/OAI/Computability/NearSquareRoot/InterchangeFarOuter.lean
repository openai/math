import Mathlib.SetTheory.Cardinal.Finite
import OAI.Computability.NearSquareRoot.InterchangeIncidence

/-!
# Products of directed rectangles on the outer labels

An outer key specifies the changing coordinates, one inner rectangle on each of
those coordinates, and a common inner word on every other coordinate.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OuterRectangles

variable {ι A K : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]

abbrev Key (ι A K : Type*) [DecidableEq ι] (p : ℕ) :=
  (s : {s : Finset ι // s.card = p}) × ((↑s.val → K) × ({i // i ∉ s.val} → A))

def Incident (I : Bool → K → A → Prop) {p : ℕ} (side : Bool) (r : Key ι A K p)
    (x : ι → A) : Prop :=
  (∀ i, I side (r.2.1 i) (x i)) ∧ ∀ i, r.2.2 i = x i

def differing (x y : ι → A) : Finset ι := Finset.univ.filter fun i => x i ≠ y i

omit [DecidableEq ι] in
@[simp] theorem mem_differing {x y : ι → A} {i : ι} :
    i ∈ differing x y ↔ x i ≠ y i := by simp [differing]

def Supported (far : A → A → Prop) (p : ℕ) (x y : ι → A) : Prop :=
  (differing x y).card = p ∧ ∀ i, x i ≠ y i → far (x i) (y i)

variable {I : Bool → K → A → Prop} {far : A → A → Prop} {p : ℕ}

private theorem active_eq_differing
    (irrefl : ∀ a, ¬ far a a)
    (cross : ∀ {k x y}, I false k x → I true k y → far x y)
    {r : Key ι A K p} {x y : ι → A} (hx : Incident I false r x)
    (hy : Incident I true r y) : r.1.val = differing x y := by
  ext i
  rw [mem_differing]
  constructor
  · intro hi he
    have hf := cross (hx.1 ⟨i, hi⟩) (hy.1 ⟨i, hi⟩)
    change far (x i) (y i) at hf
    exact irrefl _ (he ▸ hf)
  · contrapose!
    intro hi
    exact (hx.2 ⟨i, hi⟩).symm.trans (hy.2 ⟨i, hi⟩)

/-- Crossing a rectangle yields an off-diagonal supported pair whenever `p > 0`. -/
theorem supported_of_incident
    (irrefl : ∀ a, ¬ far a a)
    (cross : ∀ {k x y}, I false k x → I true k y → far x y)
    {r : Key ι A K p} {x y : ι → A} (hx : Incident I false r x)
    (hy : Incident I true r y) : Supported far p x y := by
  have he := active_eq_differing irrefl cross hx hy
  refine ⟨he ▸ r.1.property, fun i hi => ?_⟩
  have hr : i ∈ r.1.val := he ▸ mem_differing.mpr hi
  exact cross (hx.1 ⟨i, hr⟩) (hy.1 ⟨i, hr⟩)

/-- The outer off-diagonal support is a disjoint union of product rectangles. -/
theorem supported_iff_unique
    (irrefl : ∀ a, ¬ far a a)
    (cross : ∀ {k x y}, I false k x → I true k y → far x y)
    (cover : ∀ x y, far x y → ∃! k, I false k x ∧ I true k y)
    (x y : ι → A) :
    Supported far p x y ↔ ∃! r : Key ι A K p, Incident I false r x ∧ Incident I true r y := by
  classical
  constructor
  · rintro ⟨hcard, hfar⟩
    let S : {s : Finset ι // s.card = p} := ⟨differing x y, hcard⟩
    have unique (i : S.val) : ∃! k, I false k (x i) ∧ I true k (y i) :=
      cover _ _ (hfar i (mem_differing.mp i.property))
    let f : ↑S.val → K := fun i => (unique i).exists.choose
    have hf (i : S.val) : I false (f i) (x i) ∧ I true (f i) (y i) :=
      (unique i).exists.choose_spec
    let g : {i // i ∉ S.val} → A := fun i => x i
    refine ⟨⟨S, f, g⟩, ⟨⟨fun i => (hf i).1, fun _ => rfl⟩,
      ⟨fun i => (hf i).2, fun i => ?_⟩⟩, ?_⟩
    · exact not_ne_iff.mp (fun h => i.property (mem_differing.mpr h))
    · rintro ⟨T, f', g'⟩ ⟨hx, hy⟩
      have he : T = S := Subtype.ext (active_eq_differing irrefl cross hx hy)
      subst T
      have hfg : f' = f := funext fun i => (unique i).unique ⟨hx.1 i, hy.1 i⟩ (hf i)
      have hgg : g' = g := funext fun i => hx.2 i
      cases hfg
      cases hgg
      rfl
  · rintro ⟨r, ⟨hx, hy⟩, _⟩
    exact supported_of_incident irrefl cross hx hy

/-- Number of far coordinates across a rectangle. -/
theorem count_far_cross [DecidableRel far]
    (irrefl : ∀ a, ¬ far a a)
    (cross : ∀ {k x y}, I false k x → I true k y → far x y)
    {r : Key ι A K p} {x y : ι → A} (hx : Incident I false r x)
    (hy : Incident I true r y) :
    (Finset.univ.filter fun i => far (x i) (y i)).card = p := by
  have h := supported_of_incident irrefl cross hx hy
  suffices Finset.univ.filter (fun i => far (x i) (y i)) = differing x y by
    rw [this, h.1]
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_differing]
  exact ⟨fun hf he => irrefl _ (he ▸ hf), h.2 i⟩

omit [DecidableEq A] in
/-- Inner side separation gives zero far coordinates within either outer side. -/
theorem count_far_same [DecidableRel far]
    (irrefl : ∀ a, ¬ far a a)
    (sep : ∀ {side k x y}, I side k x → I side k y → ¬ far x y)
    {side : Bool} {r : Key ι A K p} {x y : ι → A}
    (hx : Incident I side r x) (hy : Incident I side r y) :
    (Finset.univ.filter fun i => far (x i) (y i)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _
  by_cases hi : i ∈ r.1.val
  · exact sep (hx.1 ⟨i, hi⟩) (hy.1 ⟨i, hi⟩)
  · have he := (hx.2 ⟨i, hi⟩).symm.trans (hy.2 ⟨i, hi⟩)
    change x i = y i at he
    rw [he]
    exact irrefl _

open scoped Classical in
omit [DecidableEq A] in
/-- Outer incidence is the number of choices of active coordinates times the product
of the inner incidence bounds on those coordinates. -/
theorem card_incident_le [Fintype K] [Fintype A] (side : Bool) (x : ι → A) {B : ℕ}
    (h : ∀ i, Fintype.card {r : K // I side r (x i)} ≤ B) :
    Fintype.card {r : Key ι A K p // Incident I side r x} ≤
      (Fintype.card ι).choose p * B ^ p := by
  have h' := Rectangles.card_incident_active_complement p K A (fun i r => I side r (x i)) x h
  calc
    _ = Nat.card {r : Key ι A K p // Incident I side r x} := (@Nat.card_eq_fintype_card _ _).symm
    _ ≤ _ := by
      simp only [← Nat.card_eq_fintype_card] at h'
      rw [← Nat.card_eq_fintype_card (α := ι)]
      exact h'

end OuterRectangles

end NearSquareRoot
end Computability
end OAI
