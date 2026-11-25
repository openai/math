import OAI.Computability.BorderVNP.DiagonalBottomSubstitution
import OAI.Computability.BorderVNP.DiagonalExternalSewFactory
import OAI.Computability.BorderVNP.ParseBatchWiredWitnessTape

/-! # Grouped bottom substitution on the actual programmed tape and team wires -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing Diagonal Diagonal.CellEntries Cover TeamContraction ParseBatch ParseBatchVerifier
open Prewire Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts PhysicalEpochs VPVNP VPVNP.ParseGrammar MvPolynomial
open scoped BigOperators Classical

variable {R r pins link k D q depth a regs w e width s copies groups : ℕ}
    (count : groups*copies = R+1)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs w e width ≤ k+1)
    {order : Fin (tileCount q depth) ≃ (Fin q → Deck (depth+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D q depth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

private theorem product_teams {teams packs copies : ℕ} {E : Type*} [CommMonoid E]
    (e : Fin packs × Fin copies ≃ Fin teams) (v : Fin teams → E) :
    (∏ i, v i) = ∏ j, ∏ c, v (e (j,c)) := by
  have h := e.prod_comp v
  rw [Fintype.prod_prod_type] at h
  exact h.symm

/-- On all later literal tails, the true initial bundles' polynomial tensor
sum equals the substituted row of the physical input layout. The exterior
wire choices are shared across teams and the interior wires have already
been summed separately inside each routed verifier. -/
theorem tape_groups {Gadget E : Type} [Field E] (values : Gadget → E)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (pin : Fin pins → Bool) :
    let G := tapeWiring p free (Wires.ownerSlots (r := r) (k := regs) (w := w) (e := e) (W := width))
      pins link (k+1) fit
    substituted E k s G.slot pin =
      ∑ ext : Exterior R r link → Bool, ∏ i : Fin (groups), ∑ z : Fin copies → W.Hidden position,
        ((W.bundle position copies z).valued values).tensor (fun b =>
          FineView.extend (groupedLane G (tileCount q depth) Fintype.card_pos groups copies count)
            (fun p _ => publicBits G p.1 pin ext p.2) (i,b)) := by
  intro G
  let state : ParseTable.State (Fin (k+1) × Bool) s := 0
  let d := Fin.last k
  rw [substituted_wired_queries]
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro ext _
  let team := (teamBlocks (groups) copies count).symm
  let value := fun u => MvPolynomial.map (Int.castRingHom E)
    (∑ int : Wires.Edge r regs w e width → Bool, ∏ j : Fin r, labelQuery d state (G.word pin ext int u j))
  refine Eq.trans ?_ ((product_teams team value).trans ?_)
  · apply Finset.prod_congr (Finset.ext fun _ => by simp)
    intro u _
    apply congrArg (MvPolynomial.map (Int.castRingHom E))
    exact Finset.sum_congr (Finset.ext fun _ => by simp) fun _ _ => rfl
  apply Finset.prod_congr rfl
  intro i _
  let y := fun b => FineView.extend (groupedLane G (tileCount q depth) Fintype.card_pos groups copies count)
            (fun p _ => publicBits G p.1 pin ext p.2) (i,b)
  let fields := fun c => publicBits G (team (i,c)) pin ext
  refine Eq.trans ?_ (W.bundle_read position values copies y fields
    (fun c v => grouped_publicBits G Fintype.card_pos (groups) copies count pin ext i c v)).symm
  apply Finset.prod_congr rfl
  intro c _
  apply congrArg (MvPolynomial.map (Int.castRingHom E))
  refine Eq.trans ?_ ((wired_queries_actual G d state (team (i,c)) pin ext).symm.trans ?_)
  · exact Finset.sum_congr (Finset.ext fun _ => by simp) fun _ _ => rfl
  exact Finset.sum_congr (Finset.ext fun _ => by simp) fun _ _ => rfl

/-- Apply the grouped-input identity to the row-major leaves of an actual
public site factory, with the same program and literal field on both sides. -/
theorem tape_bottom {K : Type} [Field K] (F : Factory D K) {T : ℕ} (count : F.fan^T*copies = R+1)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs w e width ≤ k+1)
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D q depth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {Gadget E : Type} [Field E] (values : Gadget → E)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (pin : Fin pins → Bool) :
    let G := tapeWiring p free (Wires.ownerSlots (r := r) (k := regs) (w := w) (e := e) (W := width))
      pins link (k+1) fit
    substituted E k s G.slot pin =
      ∑ ext : Exterior R r link → Bool, ∏ i : Fin (F.fan^T), ∑ z : Fin copies → W.Hidden position,
        ((W.bundle position copies z).valued values).tensor (fun b =>
          factoryInputs F G q depth count pin ext (i,b)) :=
  W.tape_groups count p fit position values free pin

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
