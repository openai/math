import OAI.Computability.BorderVNP.DiagonalInitialGridBundle
import OAI.Computability.BorderVNP.ParseBooleanPowerSites
import OAI.Computability.BorderVNP.PackedGridBatch
import OAI.Computability.BorderVNP.PackedGridSlots

/-! # Conditioned public placement of a physical weighted Boolean verifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPlacement

open Crossing Diagonal.CellEntries Shortening ParseBatch VPVNP.BooleanTranscript
open scoped BigOperators Classical

private theorem filters_equal {α : Type*} (f g : Fintype α) {p q : α → Prop}
    (i : DecidablePred p) (j : DecidablePred q) (he : ∀ a, p a ↔ q a) :
    (@Finset.filter α p i (@Finset.univ α f)).card = (@Finset.filter α q j (@Finset.univ α g)).card := by
  congr 1
  ext a
  simp [he]

/-- Place the *already rewired* verifier, routing its private edges inside
the grid and keeping exactly its public leaf numbering at the boundary. -/
theorem tagged_verifier_bundle {D n s b : ℕ} {X W Param Gadget G J : Type}
    [Fintype X] [Fintype W] [Fintype Param] [Group G] [Fintype G] [Fintype J]
    (c : Circuit (X ⊕ W) s) (weighted : Param × Fin b → W)
    (volume h copies : ℕ) (size : (BooleanLayout.layout c weighted).network.bitVolume ≤ volume)
    (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) (step : J → G)
    (invStep : ∀ j, ∃ k, step k = (step j)⁻¹) (short : ∀ u : G, ∃ w : List J, w.length ≤ h ∧ (w.map step).prod = u)
    (input : X ≃ Fin n) (order : Fin (Fintype.card G) ≃ G) (slots : ℕ) (fit : n ≤ slots) :
    let M := (publicGridSlots position step input order (fun _ => 1) slots fit volume h).repeatGrid copies
    ∃ (Hidden : Type) (_ : Fintype Hidden) (term : Hidden → M.Tables (Entry Param Gadget)),
      (∀ z, Nonempty (PowerWords (Fin copies × Unit) Param Gadget b M (term z))) ∧
      ∀ (E : Type*) [CommRing E] (values : Gadget → E) (x : Fin copies → X → Bool),
        (∑ z, M.value (fun v a y => interpret values (term z v a y)) (fun p _ => x p.1 p.2)) =
        ∏ i, MvPolynomial.map (Int.castRingHom E) ((BooleanLayout.layout c weighted).network.value
          ((BooleanLayout.layout c weighted).tables (BooleanLayout.factor c BooleanLayout.powerWeight)) (fun p _ => x i p)) := by
  let L := BooleanLayout.layout c weighted
  let N := L.network.inDimension D
  let tags : N.Tables (Entry Param Gadget) := BooleanLayout.powerTags c weighted
  let sites : PowerSites Unit Param Gadget b N tags :=
    ⟨(BooleanLayout.powerSites c weighted).site, (BooleanLayout.powerSites c weighted).named,
      (BooleanLayout.powerSites c weighted).other⟩
  have size' : Fintype.card N.Site ≤ volume :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans size)
  obtain ⟨route⟩ := routed_public_slots step input order N L.distinct_input_leaves slots fit invStep size'
    (fun v => by
      apply le_trans _ (BooleanLayout.degree_bound c weighted v)
      have hu := L.internal_degree v
      exact le_trans (le_of_eq (congrArg₂ (· + ·)
        (filters_equal _ _ _ _ fun _ => Iff.rfl) (filters_equal _ _ _ _ fun _ => Iff.rfl)))
        (hu.trans (le_of_eq (filters_equal _ _ _ _ fun _ => Iff.rfl)))) short
  dsimp only
  rw [← grid_eq_public_slots position step input order N L.distinct_input_leaves slots fit]
  obtain ⟨H,inst,term,words,eqv⟩ :=
    exists_privateBundle_terms position route (fun _ => le_rfl) sites copies
  refine ⟨H,inst,term,words,?_⟩
  intro E _ values x
  refine (eqv E values (fun p _ => x p.1 p.2)).trans ?_
  exact Finset.prod_congr rfl fun i _ => BooleanLayout.powerTags_value c weighted values (x i)

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI
