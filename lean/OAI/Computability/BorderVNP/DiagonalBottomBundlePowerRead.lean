import OAI.Computability.BorderVNP.DiagonalOuterPowerRead
import OAI.Computability.BorderVNP.DiagonalBottomSubstitution
import OAI.Computability.BorderVNP.PackedGridSelectedRead

/-! # The individual power flag in a surviving bottom bundle

Each retained tile can have its own reconstructed endpoint words. The selected
copy reads its own cable slice and its numbered grouped exterior lane. A
passing product has all its constituent copies present.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Packing
open scoped Classical

variable {D exp copies : ℕ} {Team Param Gadget P A H : Type}
  [Fintype Team] [Fintype Param]
  {N : Network D P (fun _ => 1)} (width : A → ℕ) (lane : P ↪ Σ a, Fin (width a)) (owner : A → N.Site)

/-- The actual local copy slice, including the grouped port bit at its concrete address. -/
def PowerInput.groupedCopy (i : Fin copies) (x : PowerInput (N.groupedRepeat width owner copies)) : PowerInput N :=
  ⟨fun e => Profile.blocks (x.edges e) i,fun p _ => let a := Network.repeatLane width lane copies (i,p); x.ports a.1 a.2⟩

variable (aligned : ∀ p, owner (lane p).1 = N.attach p) (t : H → Tracked Team Param Gadget exp N)
  (z : Fin copies → H) (w : PowerSlot (Fin copies × Team) Param exp)
  (x : PowerInput (N.groupedRepeat width owner copies))

/-- The grouped product uses the chosen copy's power word exactly when every copy
in this retained site passes. -/
theorem Tracked.groupedCopies_power_read (live : ∀ i, N.read (t (z i)).tags (x.groupedCopy width lane owner i).edges
    (x.groupedCopy width lane owner i).ports ((t (z w.1.1)).words.site (w.1.2,w.2)) ≠ 0) :
    (Tracked.groupedCopies width lane owner aligned t z).powerRead w x =
    (t (z w.1.1)).powerRead (w.1.2,w.2) (x.groupedCopy width lane owner w.1.1) := by
  let v := (t (z w.1.1)).words.site (w.1.2,w.2)
  let parts := fun i : Fin copies => N.read (t (z i)).tags (x.groupedCopy width lane owner i).edges
    (x.groupedCopy width lane owner i).ports v
  have pass : (∏ i, parts i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => live i
  change (if (∏ i, parts i) = 0 then false else _) = _
  rw [ite_eq_right pass]
  rfl

/-- Read the original hidden table through the equality identifying its routed
fine network with the fixed public bottom directory. -/
theorem Tracked.castLayout_power_read {bits : P → ℕ} {L M : Network D P bits} (h : L = M)
    (s : Tracked Team Param Gadget exp L) (slot : PowerSlot Team Param exp) (a : PowerInput M) :
    (s.castLayout h).powerRead slot a = s.powerRead slot (Eq.mpr (congrArg PowerInput h) a) := by
  subst M
  rfl

/-- Arbitrary other copies read their tag at the chosen copy's site across
the same genuine layout equality. -/
theorem Tracked.castLayout_copy_tag {bits : P → ℕ} {L M : Network D P bits} (h : L = M)
    (s other : Tracked Team Param Gadget exp L) (slot : PowerSlot Team Param exp) (a : PowerInput M) :
    M.read (other.castLayout h).tags a.edges a.ports ((s.castLayout h).words.site slot) =
      L.read other.tags (Eq.mpr (congrArg PowerInput h) a).edges (Eq.mpr (congrArg PowerInput h) a).ports (s.words.site slot) := by
  subst M
  rfl

end Diagonal.CellEntries

namespace Packing.DeckGrid.WiredWitness

set_option maxHeartbeats 1600000

open Crossing Diagonal.CellEntries Cover TeamContraction ParseBatch ParseBatchVerifier
open Prewire Diagonal.ExternalSew.GridHosts VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g D q depth : ℕ} {Edge Gadget : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {state : Fin g}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {copies : ℕ} (z : Fin copies → W.Hidden position)

private abbrev width (g : ℕ) := fun _ : Fin g => blockWidth (r*n) g
private noncomputable abbrev top :=
  (wiredGrid G q depth order position).groupedRepeat (width (r := r) (n := n) (Fintype.card (Fin q → Deck (depth+2)))) order copies

/-- Slice one retained public tile and transport its true wires/ports back
onto the routed fine network of this witness. -/
noncomputable def seedCopyInput (a : PowerInput (top (G := G) position (copies := copies) (order := order))) (i : Fin copies) :
    PowerInput (W.seedGrid position) :=
  Eq.mpr (congrArg PowerInput (W.seedGrid_eq position)) (a.groupedCopy _ (wiredLane G _ Fintype.card_pos) order i)

/-- At a passing original tile, its actual grouped copy's power slot is exactly
the fine verifier's selected bit on the reconstructed cable and exterior lanes. -/
theorem bundle_power_read (w : PowerSlot (Fin copies × Unit) (GrammarLabel (Fin n × Bool) (Fin g) n)
      (Nat.clog 2 (r*(2*d.val+1)+1))) (a : PowerInput (top (G := G) position (copies := copies) (order := order)))
    (live : ∀ i, (W.seedGrid position).read (W.seedTags (Gadget := Gadget) position (z i))
      (W.seedCopyInput position a i).edges (W.seedCopyInput position a i).ports
      ((W.seedWords (Gadget := Gadget) position (z w.1.1)).site (w.1.2,w.2)) ≠ 0) :
    (W.bundle (Gadget := Gadget) position copies z).powerRead w a =
      (W.seedGrid position).read (W.seedWords (Gadget := Gadget) position (z w.1.1)).selected
        (W.seedCopyInput position a w.1.1).edges (W.seedCopyInput position a w.1.1).ports
        ((W.seedWords (Gadget := Gadget) position (z w.1.1)).site (w.1.2,w.2)) (w.1.2,w.2) := by
  let base (i : Fin copies) := (⟨W.seedTags (Gadget := Gadget) position (z i),W.seedWords position (z i)⟩ :
    Tracked Unit _ Gadget _ (W.seedGrid position))
  let read (i : Fin copies) : PowerInput (wiredGrid G q depth order position) :=
    PowerInput.groupedCopy (N := wiredGrid G q depth order position) _ (wiredLane G (Fintype.card (Fin q → Deck (depth+2))) Fintype.card_pos) order i a
  let original := W.seedGrid_eq position
  have alive (i : Fin copies) : (wiredGrid G q depth order position).read (W.seed (Gadget := Gadget) position (z i)).tags
      (read i).edges (read i).ports ((W.seed (Gadget := Gadget) position (z w.1.1)).words.site (w.1.2,w.2)) ≠ 0 := by
    intro fail
    exact live i ((Tracked.castLayout_copy_tag original (base w.1.1) (base i) (w.1.2,w.2) (read i)).symm.trans fail)
  let l := wiredLane G (Fintype.card (Fin q → Deck (depth+2))) Fintype.card_pos
  have h := Tracked.groupedCopies_power_read (N := wiredGrid G q depth order position)
    (width (r := r) (n := n) (Fintype.card (Fin q → Deck (depth+2)))) l order (wired_aligned G q depth order position)
    (W.seed (Gadget := Gadget) position) z w a alive
  exact h.trans (Tracked.castLayout_power_read original (base w.1.1) (w.1.2,w.2) (read w.1.1))


end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
