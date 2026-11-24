import OAI.Computability.VPVNP.ParseIncidenceDefs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-! # Finite Boolean coordinates for ordered parse occurrences

The coordinates bound the start, layer and binary split independently. This rectangular
index set includes candidate productions which may be ruled out by the local grammar
conditions. Its cardinality is polynomial in the degree cutoff and the alphabet sizes.
A Boolean word specifies a finite table by its characteristic function on these coordinates.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

/-- An occurrence fits the coordinate table if all its numerical fields are below `D`. -/
def ParseEvent.Bounded {V H : Type*} (e : ParseEvent V H) (D : ℕ) : Prop :=
  e.start < D ∧ e.layer < D ∧ match e.production with
    | .inl _ => True
    | .inr (b, _, _) => b < D

theorem ParseEvent.bounded_of_wellFormed {V H : Type*} (e : ParseEvent V H)
    (h : e.WellFormed) {D : ℕ} (hs : e.start < D) (hl : e.layer < D) : e.Bounded D := by
  refine ⟨hs, hl, ?_⟩
  cases hp : e.production with
  | inl v => trivial
  | inr s =>
    rcases s with ⟨b, i, j⟩
    have hb : b < e.layer := by simpa [ParseEvent.WellFormed, hp] using h
    exact hb.trans hl

/-- A candidate event has an interval, parent state and either a terminal or a split
together with the two ordered child states. -/
abbrev EventCode (V H : Type*) (D : ℕ) :=
  Fin D × Fin D × H × (V ⊕ (Fin D × H × H))

namespace EventCode

variable {V H : Type*} {D : ℕ}

/-- Decode a candidate event by taking the natural values of its start, layer and binary split
indices. -/
def event (c : EventCode V H D) : ParseEvent V H :=
  ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.map id (fun (b, i, j) => (b.val, i, j))⟩

theorem event_bounded (c : EventCode V H D) : c.event.Bounded D := by
  rcases c with ⟨l, d, h, v | ⟨b, i, j⟩⟩
  · exact ⟨l.isLt, d.isLt, trivial⟩
  · exact ⟨l.isLt, d.isLt, b.isLt⟩

/-- The coordinate tuple is recovered from the natural-valued event and its bounds. -/
def ofEvent (e : ParseEvent V H) (he : e.Bounded D) : EventCode V H D :=
  (⟨e.start, he.1⟩, ⟨e.layer, he.2.1⟩, e.state, match hp : e.production with
    | .inl v => .inl v
    | .inr (b, i, j) => .inr (⟨b, by simpa [hp] using he.2.2⟩, i, j))

@[simp] theorem event_ofEvent (e : ParseEvent V H) (he : e.Bounded D) :
    (ofEvent e he).event = e := by
  rcases e with ⟨l, d, h, v | ⟨b, i, j⟩⟩ <;> rfl

@[simp] theorem ofEvent_event (c : EventCode V H D) : ofEvent c.event (event_bounded c) = c := by
  rcases c with ⟨l, d, h, v | ⟨b, i, j⟩⟩ <;> rfl

/-- The bijection between event codes with indices in `Fin D` and parse events whose start,
layer and binary split are below `D`. -/
def boundedEquiv : EventCode V H D ≃ {e : ParseEvent V H // e.Bounded D} where
  toFun c := ⟨c.event, c.event_bounded⟩
  invFun e := ofEvent e.1 e.2
  left_inv := ofEvent_event
  right_inv e := Subtype.ext (event_ofEvent e.1 e.2)

theorem event_injective : Function.Injective (event (V := V) (H := H) (D := D)) :=
  fun _ _ h => boundedEquiv.injective (Subtype.ext h)

variable (V H) [Fintype V] [Fintype H] (D : ℕ)

theorem card : Fintype.card (EventCode V H D) =
    D * D * Fintype.card H * (Fintype.card V + D * Fintype.card H * Fintype.card H) := by
  simp [EventCode, Nat.mul_assoc]

/-- Enumerate the rectangular coordinate set with a single finite address. -/
noncomputable def enumerate (i : Fin (Fintype.card (EventCode V H D))) : ParseEvent V H :=
  event ((Fintype.equivFin (EventCode V H D)).symm i)

theorem enumerate_injective : Function.Injective (enumerate V H D) :=
  event_injective.comp (Fintype.equivFin _).symm.injective

theorem enumerate_bounded (i : Fin (Fintype.card (EventCode V H D))) :
    (enumerate V H D i).Bounded D := event_bounded _

theorem exists_enumerate_iff (e : ParseEvent V H) :
    (∃ i, enumerate V H D i = e) ↔ e.Bounded D := by
  constructor
  · rintro ⟨i, rfl⟩
    exact enumerate_bounded V H D i
  · intro he
    refine ⟨Fintype.equivFin _ (ofEvent e he), ?_⟩
    simp [enumerate]

/-- Table of all occurrences whose enumerated Boolean flags are set. -/
noncomputable def selected (x : Fin (Fintype.card (EventCode V H D)) → Bool) :
    Finset (ParseEvent V H) := by
  classical
  exact (Finset.univ.filter (fun i => x i = true)).image (enumerate V H D)

theorem mem_selected (x : Fin (Fintype.card (EventCode V H D)) → Bool) (e : ParseEvent V H) :
    e ∈ selected V H D x ↔ ∃ i, x i = true ∧ enumerate V H D i = e := by
  classical
  simp [selected]

@[simp] theorem enumerate_mem_selected (x : Fin (Fintype.card (EventCode V H D)) → Bool)
    (i : Fin (Fintype.card (EventCode V H D))) :
    enumerate V H D i ∈ selected V H D x ↔ x i = true := by
  rw [mem_selected]
  constructor
  · rintro ⟨j, hj, h⟩
    exact (enumerate_injective V H D h) ▸ hj
  · exact fun hi => ⟨i, hi, rfl⟩

/-- Boolean words and bounded occurrence tables are in bijection, without additional
bits for unused events or auxiliary witnesses. -/
noncomputable def selectedEquiv : (Fin (Fintype.card (EventCode V H D)) → Bool) ≃
    {T : Finset (ParseEvent V H) // ∀ e ∈ T, e.Bounded D} := by
  classical
  exact {
    toFun := fun x => ⟨selected V H D x, fun e he =>
      let ⟨i, _, hi⟩ := (mem_selected V H D x e).mp he
      hi ▸ enumerate_bounded V H D i⟩
    invFun := fun T i => decide (enumerate V H D i ∈ T.1)
    left_inv := fun x => by
      funext i
      simp
    right_inv := fun T => by
      apply Subtype.ext
      ext e
      rw [mem_selected]
      constructor
      · rintro ⟨i, hi, rfl⟩
        simpa using hi
      · intro he
        obtain ⟨i, hi⟩ := (exists_enumerate_iff V H D e).mpr (T.2 e he)
        exact ⟨i, by simpa [hi] using he, hi⟩ }

@[simp] theorem selectedEquiv_apply (x : Fin (Fintype.card (EventCode V H D)) → Bool) :
    (selectedEquiv V H D x).1 = selected V H D x := rfl

end EventCode
end ParseGrammar

end VPVNP
end Computability
end OAI
