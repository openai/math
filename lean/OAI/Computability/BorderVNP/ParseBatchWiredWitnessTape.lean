import OAI.Computability.BorderVNP.ParseBatchWiredWitnessValue

/-! # A named routed witness chosen before the private tape literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Crossing Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar MvPolynomial
open scoped BigOperators Classical

variable {D q depth R r pins link k a regs w e width : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(cutWidth (k+1)+a))+R*link+
      Wires.innerWidth r regs w e width ≤ k+1)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))

/-- The shared zero-literal layout on the actual tape sorter and register-frame wires. -/
abbrev tapeTemplate (pins : ℕ) :=
  tapeWiring p (fun _ _ (_ : Fin a) => false)
    (Wires.ownerSlots (r := r) (k := regs) (w := w) (e := e) (W := width)) pins link (k+1) fit

/-- The real degree-component table and its designated root slot on the
fixed zero-tail tape wiring. A witness can be selected before any literal installation. -/
theorem exists_tapeWitness (s : ℕ) (hr : ((k+1)+s+2)^24 ≤ r) :
    Nonempty (WiredWitness (tapeTemplate p fit pins) (Fin.last k) D q depth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s)) := by
  have hr₀ : 0 < r := (Nat.pow_pos (by omega : 0 < (k+1)+s+2)).trans_le hr
  exact exists_wiredWitness _ _ _ _ _ _ _ s rfl (by simp [Nat.mul_comm]) hr
    (tape_edges_le r regs w e width hr₀)

namespace WiredWitness

variable {s : ℕ} {order}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D q depth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- After the private literal tail is installed, the *original named* zero-template
witness has the desired physical team contraction. Its site names, private routes,
hidden assignments and tagged local table functions are retained. -/
theorem tape_seed_value {Gadget : Type} {E : Type*} [CommRing E] (values : Gadget → E)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (team : Fin (R+1))
    (pin : Fin pins → Bool) (ext : Exterior R r link → Bool) :
    let G := tapeWiring p free (Wires.ownerSlots (r := r) (k := regs) (w := w) (e := e) (W := width)) pins link (k+1) fit
    (∑ z : W.Hidden position, (W.seedGrid position).value
      (fun v b x => interpret values (W.seedTags position z v b x)) (fun j _ => publicBits G team pin ext j)) =
    MvPolynomial.map (Int.castRingHom E) (∑ int : Wires.Edge r regs w e width → Bool,
      ∏ j, labelQuery (Fin.last k) (0 : ParseTable.State (Fin (k+1) × Bool) s) (G.word pin ext int team j)) := by
  intro G
  refine (W.seed_value position values (publicBits G team pin ext)).trans ?_
  apply congrArg (MvPolynomial.map (Int.castRingHom E))
  refine (wired_queries_actual G (Fin.last k) (0 : ParseTable.State (Fin (k+1) × Bool) s) team pin ext).trans ?_
  exact Finset.sum_congr (Finset.ext fun _ => by simp) fun _ _ => rfl

end WiredWitness
end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
