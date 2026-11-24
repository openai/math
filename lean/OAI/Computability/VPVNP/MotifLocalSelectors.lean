import OAI.Computability.VPVNP.MotifSelector
import OAI.Computability.VPVNP.WireTensor

/-!
# Local selector checks inside wire tensors

The selector carried by each edge is read at its two incident parties. This
realizes the global selector sum as a contraction of one wire network, and
retains the payload on each individual edge.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifSelector

open WireTensor

variable {J E S R : Type*}

/-- Half-wire coordinates local to one party. -/
abbrev Half (G : Supply J E) (I : E → Type*) (j : J) :=
  ((e : E) → j = G.src e → I e) × ((e : E) → j = G.dst e → I e)

/-- Apply a separate coordinate transformation at each incident wire. -/
def mapHalf {I I' : E → Type*} (G : Supply J E) {j : J} (f : ∀ e, I e → I' e)
    (x : Half G I j) : Half G I' j :=
  (fun e h => f e (x.1 e h), fun e h => f e (x.2 e h))

theorem mapHalf_edgeAssignment {I I' : E → Type*} (G : Supply J E) (j : J)
    (f : ∀ e, I e → I' e) (x : ∀ e, I e) :
    mapHalf G f (edgeAssignment G.src G.dst x j) =
      edgeAssignment G.src G.dst (fun e => f e (x e)) j := rfl

/-- Read the chosen incident edge through its appropriate half-wire. -/
noncomputable def readAnchor (G : Supply J E) {I : E → Type*} (j : J) (x : Half G I j) :
    I (G.anchor j) := by
  classical
  exact if h : j = G.src (G.anchor j) then x.1 (G.anchor j) h else
    x.2 (G.anchor j) ((G.anchor_incident j).resolve_left (fun he => h he.symm)).symm

@[simp] theorem readAnchor_edgeAssignment (G : Supply J E) {I : E → Type*} (j : J)
    (x : ∀ e, I e) : readAnchor G j (edgeAssignment G.src G.dst x j) = x (G.anchor j) := by
  unfold readAnchor
  split <;> rfl

/-- A party checks that all of its incident edges carry its anchor selector. -/
def HalfAgrees (G : Supply J E) {I : E → Type*} (j : J) (x : Half G (fun e => S × I e) j) :
    Prop :=
  (∀ e (h : j = G.src e), (x.1 e h).1 = (readAnchor G j x).1) ∧
    (∀ e (h : j = G.dst e), (x.2 e h).1 = (readAnchor G j x).1)

@[simp] theorem halfAgrees_edgeAssignment (G : Supply J E) {I : E → Type*} (j : J)
    (x : ∀ e, S × I e) :
    HalfAgrees G j (edgeAssignment G.src G.dst x j) ↔ Agrees G (fun e => (x e).1) j := by
  unfold HalfAgrees Agrees
  rw [readAnchor_edgeAssignment]
  constructor
  · rintro ⟨h₁, h₂⟩ e (he | he)
    · exact h₁ e he.symm
    · exact h₂ e he.symm
  · intro h
    exact ⟨fun e he => h e (Or.inl he.symm), fun e he => h e (Or.inr he.symm)⟩

open scoped Classical in
/-- Carry selector and payload on every supply edge and use only the payload
in the original map after the selectors have been checked. -/
noncomputable def selectedMap [Zero R] {I : E → Type*} {C : J → Type*} (G : Supply J E)
    (L : ∀ (_ : S) (j : J), C j → Half G I j → R) (j : J)
    (c : C j) (x : Half G (fun e => S × I e) j) : R :=
  if HalfAgrees G j x then
    L (readAnchor G j x).1 j c (mapHalf G (fun _ => Prod.snd) x) else 0

open scoped Classical in
/-- Exact local-map implementation of the selector sum in Theorem 6.1. -/
theorem applyLocal_selectedMap [Nonempty J] [Fintype J] [Fintype E] [Fintype S]
    [CommSemiring R] {I : E → Type*} [∀ e, Fintype (I e)] {C : J → Type*} (G : Supply J E)
    (L : ∀ (_ : S) (j : J), C j → Half G I j → R) :
    applyLocal (B := (wireNetwork (k := R) G.src G.dst (fun e => S × I e)).Basis)
      (selectedMap G L) (wireNetwork G.src G.dst (fun e => S × I e)).coeff =
      ∑ s, applyLocal (B := (wireNetwork (k := R) G.src G.dst I).Basis)
        (L s) (wireNetwork G.src G.dst I).coeff := by
  classical
  funext c
  rw [Finset.sum_apply]
  erw [applyLocal_wireNetwork G.src G.dst (fun e => S × I e) (selectedMap G L) c]
  have he (s : S) := applyLocal_wireNetwork G.src G.dst I (L s) c
  simp_rw [he]
  let eqv := Equiv.arrowProdEquivProdArrow E (fun _ => S) I
  rw [← eqv.symm.sum_comp, Fintype.sum_prod_type]
  simp only [selectedMap, halfAgrees_edgeAssignment, readAnchor_edgeAssignment,
    mapHalf_edgeAssignment]
  change (∑ x : E → S, ∑ y : ∀ e, I e,
    ∏ j, if Agrees G x j then L (x (G.anchor j)) j (c j) (edgeAssignment G.src G.dst y j)
      else 0) = _
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset S))]
  exact Finset.sum_congr rfl fun y _ =>
    sum_local_checks G (fun j s => L s j (c j) (edgeAssignment G.src G.dst y j))

end MotifSelector

end VPVNP
end Computability
end OAI
