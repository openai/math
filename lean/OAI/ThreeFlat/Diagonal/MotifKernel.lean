import OAI.Computability.VPVNP.MotifBase
import OAI.ThreeFlat.Diagonal.WireRewrite
import Mathlib.Logic.Equiv.Basic

namespace OAI
/-! # Co-locating motif maps and summing the absorbed internal wires

A motif term places each of its original parties at a site. Each supply
wire with both ends at one site is summed within that site; each surviving
wire is presented exactly once to its two sites.
-/

namespace ThreeFlat.Diagonal.MotifKernel

open Computability.VPVNP.WireTensor Computability.VPVNP.MotifBase
open scoped Classical

variable {J G E F : Type*} [Fintype J] [Fintype E] [Fintype G] [DecidableEq G]
variable (src dst : E → J) (place : J → G)

/-- Absorbed wires have a unique owner and crossing wires are shared. -/
def wireOwner (e : E) : Option G :=
  if place (src e) = place (dst e) then some (place (src e)) else none

abbrev WiresAt {I : E → Type*} (g : Option G) :=
  (e : {e // wireOwner src dst place e = g}) → I e

/-- Split a wire assignment into one shared string and private fields for
all sites. -/
def splitWires {I : E → Type*} : (∀ e, I e) ≃
    WiresAt src dst place (I := I) none × (∀ g, WiresAt src dst place (I := I) (some g)) :=
  (sitesByGroup (X := I) (wireOwner src dst place)).trans Equiv.piOptionEquivProd

/-- At each party, obtain the two incident half-basis lists directly from
the site's private indices and the shared indices. -/
def atParty {I : E → Type*} (j : J) (b : WiresAt src dst place (I := I) none)
    (a : WiresAt src dst place (I := I) (some (place j))) :
    ((e : E) → j = src e → I e) × ((e : E) → j = dst e → I e) := by
  constructor
  · rintro e rfl
    by_cases h : place (src e) = place (dst e)
    · exact a ⟨e, ite_eq_left h⟩
    · exact b ⟨e, ite_eq_right h⟩
  · rintro e rfl
    by_cases h : place (src e) = place (dst e)
    · exact a ⟨e, by simp [wireOwner, h]⟩
    · exact b ⟨e, ite_eq_right h⟩

omit [Fintype J] [Fintype E] [Fintype G] in
private theorem atParty_split {I : E → Type*} (j : J) (z : ∀ e, I e) :
    atParty src dst place j (splitWires src dst place z).1 ((splitWires src dst place z).2 (place j)) =
      edgeAssignment src dst z j := by
  apply Prod.ext <;> funext e h <;> subst j <;>
    by_cases hi : place (src e) = place (dst e) <;> simp [atParty, hi, edgeAssignment, splitWires, sitesByGroup,
      Equiv.piOptionEquivProd]

/-- A local restriction of an actual wire network admits a product of
site-local kernels after fixing only the surviving wires. -/
theorem applyLocal_eq_grouped [CommSemiring F] {I : E → Type*} [∀ e, Fintype (I e)]
    {A : J → Type*} (L : ∀ j, A j → (wireNetwork (k := F) src dst I).Basis j → F) (x : ∀ j, A j) :
    applyLocal L (wireNetwork src dst I).coeff x =
      ∑ b : WiresAt src dst place (I := I) none,
        ∏ g, ∑ a : WiresAt src dst place (I := I) (some g),
          ∏ j : {j // place j = g}, L j (x j) (atParty src dst place j b (j.2.symm ▸ a)) := by
  classical
  rw [applyLocal_wireNetwork]
  simp_rw [Fintype.prod_sum]
  let Q := splitWires src dst place (I := I)
  let E := fun (b : WiresAt src dst place (I := I) none)
      (a : ∀ g, WiresAt src dst place (I := I) (some g)) =>
    ∏ g, ∏ j : {j // place j = g}, L j (x j) (atParty src dst place j b (j.2.symm ▸ a g))
  change _ = ∑ b, ∑ a, E b a
  rw [← Fintype.sum_prod_type' E, ← Q.sum_comp (fun p => E p.1 p.2)]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Fintype.prod_fiberwise place (fun j => L j (x j) (edgeAssignment src dst z j))]
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  rintro ⟨j, rfl⟩ _
  rw [← atParty_split src dst place j z]

end ThreeFlat.Diagonal.MotifKernel

end OAI
