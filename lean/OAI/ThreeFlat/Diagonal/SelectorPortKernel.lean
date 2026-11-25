import OAI.ThreeFlat.Diagonal.MotifPayload
import OAI.LinearAlgebra.SpectralBooks.PortWiring

namespace OAI
/-! # Local selector and payload checks on the physical ports

A site reads the selector on its anchor port, compares the selectors on all
its incident ports, then evaluates a valid sequence on its own incident
payloads. The product of these local maps, summed over the physical wires,
is the ordinary sum of the selected products.
-/

namespace ThreeFlat.Diagonal.MotifOuterTerms

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped Classical BigOperators

variable {J E H Code V K : Type*} [CommSemiring K] [Fintype E] [Fintype J] [Nonempty J]
  [Fintype H] [Fintype Code] [Fintype V] [DecidableEq V]

/-- Port graph of a connected supply motif. -/
def ports (G : Supply J E) : PortGraph J E := ⟨G.src,G.dst⟩

noncomputable def anchorPort (G : Supply J E) (j : J) : (ports G).Port j := by
  classical
  by_cases h : G.src (G.anchor j) = j
  · exact ⟨(G.anchor j,false),h⟩
  · exact ⟨(G.anchor j,true),(G.anchor_incident j).resolve_left h⟩

omit [Fintype E] [Fintype J] [Nonempty J] in
private theorem anchorPort_edge (G : Supply J E) (j : J) : (anchorPort G j).1.1 = G.anchor j := by
  unfold anchorPort
  split <;> rfl

omit [Fintype E] [Fintype J] [Nonempty J] [Fintype Code] in
private theorem check_ports_iff (G : Supply J E) (j : J) (c : E → Code) :
    (∀ p : (ports G).Port j, c p.1.1 = c (G.anchor j)) ↔ Agrees G c j := by
  constructor
  · intro h e he
    rcases he with hs | hd
    · exact h ⟨(e,false),hs⟩
    · exact h ⟨(e,true),hd⟩
  · rintro h ⟨⟨e,side⟩,hp⟩
    cases side
    · exact h e (Or.inl hp)
    · exact h e (Or.inr hp)

/-- The map at one vertex evaluates only the payloads on its own ports. -/
noncomputable def checkedPort (G : Supply J E) (p : H → V) (code : H ↪ Code)
    (B : ∀ _ : V, E → Type*) (v : V) (j : J)
    (L : {s // p s = v} → (ports G).State (B v) j → K)
    (a : (ports G).State (fun e => Code × B v e) j) : K :=
  if ∀ i, (a i).1 = (a (anchorPort G j)).1 then
    decodeLocal p code v (fun _ s => L s (fun i => (a i).2)) j (a (anchorPort G j)).1
  else 0

private def splitPayload {B : E → Type*} :
    ((e : E) → Code × B e) ≃ ((e : E) → B e) × (E → Code) where
  toFun a := (fun e => (a e).2, fun e => (a e).1)
  invFun a e := (a.2 e,a.1 e)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Outer term decomposition with a genuinely local map at every vertex.
Each supply wire has one selector word and one payload word. -/
theorem contraction_checked_ports (G : Supply J E) (p : H → V) (code : H ↪ Code)
    (B : ∀ _ : V, E → Type*) [∀ v e, Fintype (B v e)]
    (L : ∀ v j, {s // p s = v} → (ports G).State (B v) j → K) :
    (∑ v, (ports G).contraction (A := fun e => Code × B v e) (fun j => checkedPort G p code B v j (L v j))) =
      ∑ s, ∑ z : ∀ e, B (p s) e, ∏ j, L (p s) j ⟨s,rfl⟩ ((ports G).atVertex z j) := by
  classical
  rw [← sum_outer_profiles G p code (fun v => ∀ e, B v e)
    (fun v z j s => L v j s ((ports G).atVertex z j))]
  apply Finset.sum_congr rfl
  intro v _
  unfold PortGraph.contraction
  rw [← (splitPayload (Code := Code) (B := B v)).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.prod_congr rfl
  intro j _
  simp only [checkedPort, splitPayload, Equiv.coe_fn_symm_mk,
    PortGraph.atVertex, anchorPort_edge, check_ports_iff, decodeLocal]
  split_ifs <;> rfl

end ThreeFlat.Diagonal.MotifOuterTerms

end OAI
