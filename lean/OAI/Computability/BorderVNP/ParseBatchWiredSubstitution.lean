import OAI.Computability.BorderVNP.ParseBatchWiredGrid
import OAI.Computability.BorderVNP.ResidueNumberedExpansion

/-! # The initial physical team contraction in the residue diagonal

The exterior assignment is shared across both endpoints of each physical link.
Every team's interior handoff and sorter variables are already private to its
placed parse verifier. Reassembling these two classes of indices gives the exact
formal substituted polynomial of Section 11.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Crossing Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar MvPolynomial
open scoped BigOperators Classical

variable {R r t pins link inner k : ℕ} {Edge : Type} [Fintype Edge]
    (G : Wiring R r t pins link inner (k+1) Edge)

/-- Reindex the full substituted table contraction as the exterior sum
of the products of independent, interior-summed team query batches. -/
theorem substituted_wired_queries (s : ℕ) (E : Type*) [CommRing E] (pin : Fin pins → Bool) :
    Diagonal.substituted E k s G.slot pin =
      ∑ ext : Exterior R r link → Bool, ∏ team : Fin (R+1), MvPolynomial.map (Int.castRingHom E)
        (∑ int : Edge → Bool, ∏ j : Fin r, labelQuery (Fin.last k)
          (0 : ParseTable.State (Fin (k+1) × Bool) s) (G.word pin ext int team j)) := by
  let eqv := assignmentEquiv (R := R) (r := r) (link := link) (Edge := Edge)
  let value := fun links : Diagonal.Layout.Wire R r link Edge → Bool =>
    ∏ proc : Fin (R+1) × Fin r, MvPolynomial.map (Int.castRingHom E)
      (ParseTable.table _ k s (Diagonal.pairedQuery G.slot pin links proc))
  trans ∑ links, value links
  · unfold Diagonal.substituted
    apply Finset.sum_congr (Finset.ext fun _ => by simp)
    intro l _
    exact Finset.prod_congr (Finset.ext fun _ => by simp) fun _ _ => rfl
  rw [← eqv.sum_comp value, Fintype.sum_prod_type]
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro ext _
  simp only [map_sum,map_prod]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro ints _
  dsimp only [value]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr (Finset.ext fun _ => by simp)
  intro u _
  apply Finset.prod_congr (Finset.ext fun _ => by simp)
  intro j _
  apply congrArg (MvPolynomial.map (Int.castRingHom E))
  exact (universal_table_query k s (fun i => (G.slot (u,j) i).read pin (assignments ext ints))).trans
    (congrArg (labelQuery (Fin.last k) (0 : ParseTable.State (Fin (k+1) × Bool) s))
      (G.read_eq pin ext ints u j))

/-- Choose the term family on the fixed physical template before selecting
the private literal tails. The routing, hidden assignment type, local tables
and unary locations serve every such tail, simultaneously for all live pins. -/
theorem tagged_before_literals {Gadget : Type} {D a K w e W : ℕ}
    (p : UniversalMachine.Program) (s q depth : ℕ)
    (fit : 2*((UniversalMachine.programPrefix p).length+(cutWidth (k+1)+a))+R*link+Wires.innerWidth r K w e W ≤ k+1)
    (hr : ((k+1)+s+2)^24 ≤ r)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) :
    let wire := Wires.ownerSlots (r := r) (k := K) (w := w) (e := e) (W := W)
    let G₀ := tapeWiring p (fun _ _ (_ : Fin a) => false) wire pins link (k+1) fit
    let M := (wiredGrid G₀ q depth order position).repeatGrid (R+1)
    let Param := Diagonal.PairedParameters k s
    ∃ (Hidden : Type) (_ : Fintype Hidden) (term : Hidden → M.Tables (Diagonal.CellEntries.Entry Param Gadget)),
      (∀ z, Nonempty (PowerWords (Fin (R+1) × Unit) Param Gadget
        (Nat.clog 2 (r*(2*k+1)+1)) M (term z))) ∧
      ∀ (free : Fin (R+1) → Fin r → Fin a → Bool) (E : Type*) [CommRing E] (values : Gadget → E)
        (pin : Fin pins → Bool),
        let G := tapeWiring p free wire pins link (k+1) fit
        (∑ ext : Exterior R r link → Bool, ∑ z, M.value (fun v b y => interpret values (term z v b y))
          (fun u _ => publicBits G u.1 pin ext u.2)) = Diagonal.substituted E k s G.slot pin := by
  intro wire G₀ M Param
  have hr0 : 0 < r := (Nat.pow_pos (by omega : 0 < (k+1)+s+2)).trans_le hr
  let d := Fin.last k
  let state : ParseTable.State (Fin (k+1) × Bool) s := 0
  obtain ⟨H,inst,term,words,eqv⟩ := tagged_wired_batch_bundle (Gadget := Gadget) G₀ q depth (R+1) d state rfl
    (by simp [Nat.mul_comm]) hr (tape_edges_le r K w e W hr0) order position
  refine ⟨H,inst,term,words,?_⟩
  intro free E _ values pin G
  rw [substituted_wired_queries]
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro ext _
  refine (eqv E values (fun u => publicBits G u pin ext)).trans ?_
  exact Finset.prod_congr rfl fun u _ =>
    congrArg (MvPolynomial.map (Int.castRingHom E)) (wired_queries_actual G d state u pin ext)

/-- On the physical tape wiring and actual sorter/handoff edge type, the sum
over the public exterior links of the repeated grid's hidden contraction equals
the entire substituted row polynomial, for every live pin and coefficient ring. -/
theorem tagged_tapeWiring_contraction {Gadget : Type} {D a K w e W : ℕ}
    (p : UniversalMachine.Program) (free : Fin (R+1) → Fin r → Fin a → Bool) (s q depth : ℕ)
    (fit : 2*((UniversalMachine.programPrefix p).length+(cutWidth (k+1)+a))+R*link+Wires.innerWidth r K w e W ≤ k+1)
    (hr : ((k+1)+s+2)^24 ≤ r)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) :
    let G := tapeWiring p free (Wires.ownerSlots (k := K) (w := w) (e := e) (W := W)) pins link (k+1) fit
    let M := (wiredGrid G q depth order position).repeatGrid (R+1)
    let Param := Diagonal.PairedParameters k s
    ∃ (Hidden : Type) (_ : Fintype Hidden) (term : Hidden → M.Tables (Diagonal.CellEntries.Entry Param Gadget)),
      (∀ z, Nonempty (PowerWords (Fin (R+1) × Unit) Param Gadget
        (Nat.clog 2 (r*(2*k+1)+1)) M (term z))) ∧
      ∀ (E : Type*) [CommRing E] (values : Gadget → E) (pin : Fin pins → Bool),
        (∑ ext : Exterior R r link → Bool, ∑ z, M.value (fun v b y => interpret values (term z v b y))
          (fun u _ => publicBits G u.1 pin ext u.2)) = Diagonal.substituted E k s G.slot pin := by
  obtain ⟨H,inst,term,words,eqv⟩ :=
    tagged_before_literals (pins := pins) (Gadget := Gadget) p s q depth fit hr order position
  exact ⟨H,inst,term,words,eqv free⟩

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
