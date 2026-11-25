import OAI.Computability.BorderVNP.PackedGridPublic
import OAI.Computability.BorderVNP.ParseBatchQueries

/-! # Placement of the polynomial query batch on the public congruence-cover grid

The ports are numbered in query-major order. The public cell list, neighbor cables,
widths, and port attachments depend on the integers in the batch and the host, while
the realized coefficient-query computation is retained in the private cell tables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

variable {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)

/-- The same fine tensor in the ambient dimension of the host. Physical cell
coordinates are supplied by the routing construction. -/
abbrev inDimension (D' : ℕ) : Network D' P bits where
  Site := N.Site
  Edge := N.Edge
  finiteSite := N.finiteSite
  finiteEdge := N.finiteEdge
  src := N.src
  dst := N.dst
  width := N.width
  attach := N.attach
  position _ := 0
  in_ball _ := by simp

end Crossing.Network

namespace Packing.DeckGrid

open BorderVNP.Cover BorderVNP.ParseBatch BorderVNP.ParseBatchVerifier
open VPVNP VPVNP.ParseGrammar VPVNP.VerifierNetwork MvPolynomial
open scoped Classical

/-- The degree-three network budget from Lemma 2.3. -/
def batchVolume (m r : ℕ) := 180000000*(m*r)*(Nat.clog 2 (2*m*r)+3)^3

private theorem filterCardEq {α : Type*} (f g : Fintype α) {p q : α → Prop}
    (dp : DecidablePred p) (dq : DecidablePred q) (eq : ∀ a, p a ↔ q a) :
    (@Finset.filter α p dp (@Finset.univ α f)).card = (@Finset.filter α q dq (@Finset.univ α g)).card := by
  congr 1
  ext a
  simp [eq]

/-- Actual public layout for the polynomial batch on the product of congruence covers.
The `r*m` leaf ordinals are consecutive within each query. -/
noncomputable def batchGrid {D : ℕ} (q depth m r : ℕ)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) :
    Crossing.Network D (Fin r × Fin m) (fun _ => 1) :=
  GridPlacement.publicGrid position (step q (depth+2)) finProdFinEquiv order (fun _ => 1)
    (batchVolume m r) (q*(1+3*depth^3))

/-- The public grid of Proposition 7.2 computes the actual product of coefficient
queries of Lemma 2.3 over the integer parameter polynomial ring. All public wires use
the uniform width, including channels that carry no private bits. -/
theorem batch_tables {D m g s r : ℕ} (q depth : ℕ) (d : Fin m) (state : Fin g)
    (hm : m = d.val+1) (hg : g ≤ 2*m+s+1) (hr : (m+s+2)^24 ≤ r)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) :
    ∃ table : (batchGrid q depth m r order position).Tables
      (MvPolynomial (GrammarLabel (Fin m × Bool) (Fin g) m) ℤ),
      ∀ x : Fin r → Fin m → Bool, (batchGrid q depth m r order position).value table
        (fun ij _ => x ij.1 ij.2) = ∏ i, labelQuery d state (x i) := by
  obtain ⟨trees,ht,hv,hd⟩ := batched_queries d state hm hg hr
  let L := queryLayout d trees
  let N := L.network.inDimension D
  have size : Fintype.card N.Site ≤ batchVolume m r :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hv)
  obtain ⟨t,hh⟩ := GridPlacement.public_tables position (step q (depth+2)) finProdFinEquiv
    order N L.distinct_input_leaves (inverse_letter q (depth+2)) size (fun _ => le_rfl)
    (fun v => by
      apply le_trans _ (hd v)
      have hu := L.internal_degree v
      exact le_trans (le_of_eq (congrArg₂ (· + ·)
        (filterCardEq _ _ _ _ fun _ => Iff.rfl) (filterCardEq _ _ _ _ fun _ => Iff.rfl)))
        (hu.trans (le_of_eq (filterCardEq _ _ _ _ fun _ => Iff.rfl))))
    (short_words q depth) (L.tables (BooleanLayout.factor (verifier d trees) unaryWeight))
  exact ⟨t,fun x => (hh (fun ij _ => x ij.1 ij.2)).trans (ht x)⟩

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
