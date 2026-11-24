import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Relation

/-!
# Synchronizing selectors on a wire motif

In Theorem 6.1 of *VP and VNP differ over every field* the same finite
selector list is carried on every supply edge. Each party checks only
its incident edges. Connectivity makes the surviving selector lists
global, with each list contributing once.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifSelector

open Relation

variable {J E S R : Type*}

/-- Endpoint data and connectedness of the supply wires, with an incident
edge chosen at each party for reading its selector. -/
structure Supply (J E : Type*) where
  /-- Party at the source of each directed supply edge. -/
  src : E → J
  /-- Party at the destination of each directed supply edge. -/
  dst : E → J
  /-- Incident edge at each party whose selector is compared with the selectors on all other
  incident edges. -/
  anchor : J → E
  anchor_incident : ∀ j, src (anchor j) = j ∨ dst (anchor j) = j
  connected : ∀ j k, ReflTransGen
    (fun u v => ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)) j k

/-- Each selector incident to the party agrees with the selector at its anchor edge. -/
def Agrees (G : Supply J E) (x : E → S) (j : J) : Prop :=
  ∀ e, (G.src e = j ∨ G.dst e = j) → x e = x (G.anchor j)

/-- All local consistency checks succeed exactly on constant assignments. -/
theorem agrees_iff_constant [Nonempty J] (G : Supply J E) (x : E → S) :
    (∀ j, Agrees G x j) ↔ ∃ s, x = fun _ => s := by
  constructor
  · intro h
    let j₀ := Classical.choice ‹Nonempty J›
    have hloc (j k : J) : x (G.anchor j) = x (G.anchor k) := by
      induction G.connected j k with
      | refl => rfl
      | @tail j' k _ step ih =>
        obtain ⟨e, ⟨hs, hd⟩ | ⟨hs, hd⟩⟩ := step
        · exact ih.trans ((h j' e (Or.inl hs)).symm.trans (h k e (Or.inr hd)))
        · exact ih.trans ((h j' e (Or.inr hd)).symm.trans (h k e (Or.inl hs)))
    exact ⟨x (G.anchor j₀), funext fun e => (h (G.src e) e (Or.inl rfl)).trans (hloc _ _)⟩
  · rintro ⟨s, rfl⟩ j e _
    rfl

open scoped Classical in
/-- Summing over all edge selectors with the local checks gives a single
sum over global selectors. The factors may vanish or cancel in the ring. -/
theorem sum_local_checks [Nonempty J] [Fintype J] [Fintype E] [Fintype S] [CommSemiring R]
    (G : Supply J E) (L : J → S → R) :
    (∑ x : E → S, ∏ j, if Agrees G x j then L j (x (G.anchor j)) else 0) =
      ∑ s : S, ∏ j, L j s := by
  classical
  let e₀ := G.anchor (Classical.choice ‹Nonempty J›)
  have hconst {s t : S} (h : (fun _ : E => s) = fun _ => t) : s = t := congrFun h e₀
  have hf (x : E → S) :
      (∏ j, if Agrees G x j then L j (x (G.anchor j)) else 0) =
        ∑ s : S, if x = (fun _ => s) then ∏ j, L j s else 0 := by
    by_cases h : ∀ j, Agrees G x j
    · obtain ⟨t, rfl⟩ := (agrees_iff_constant G x).mp h
      rw [Finset.sum_eq_single t]
      · simp [h]
      · intro s _ hs
        exact ite_eq_right (fun he => hs (hconst he).symm)
      · simp
    · obtain ⟨j, hj⟩ := not_forall.mp h
      have hleft : (∏ j, if Agrees G x j then L j (x (G.anchor j)) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
      rw [hleft]
      apply Eq.symm (Finset.sum_eq_zero _)
      intro s _
      exact ite_eq_right (fun he => h ((agrees_iff_constant G x).mpr ⟨s, he⟩))
  simp_rw [hf]
  rw [Finset.sum_comm]
  simp

end MotifSelector

end VPVNP
end Computability
end OAI
