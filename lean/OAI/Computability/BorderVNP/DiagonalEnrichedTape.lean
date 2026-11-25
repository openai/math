import OAI.Computability.BorderVNP.DiagonalNumberedTape
import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedSum

/-! # The wired polynomial row on the histories of the physical bit-frame machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedTape

open Crossing Shortening Adaptive Packing Packing.DeckGrid Cover TeamContraction ExternalSew GridHosts
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PublicCapacity VPVNP BorderVNP.Cube MvPolynomial
open scoped BigOperators Classical BorderVNP.Epoch.Cube

universe u

variable {D m start T : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {Word : ℕ → Type} [∀ t, Fintype (Word t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r pins link k axes gridDepth a regs rw ec width s copies : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
    {order : Fin (tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D axes gridDepth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (free : Fin (R+1) → Fin r → Fin a → Bool)
    {deep : S.floor+1+S.drop*T ≤ start} (count : (EnrichedOuter.fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (tileCount axes gridDepth))
      (fun _ => copies*inputBlockWidth r (k+1) axes gridDepth) shape Word j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : EnrichedOuter.Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid (tapeTemplate p fit pins) axes gridDepth order position).groupedRepeat
      (fun _ : Fin (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth) order copies)
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (hg : 0 < inputBlockWidth r (k+1) axes gridDepth)

set_option synthInstance.maxSize 4000

/-- Enumerate the true original batch numbers in the nested public history. -/
noncomputable local instance batchFinite {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j

/-- Original routed box table on the actual initial state, chosen before
the input program's private literal values are installed. -/
noncomputable def base (z : Fin copies → W.Hidden position) :
    Tracked (Fin copies × Unit) (PairedParameters k s) Gadget (Nat.clog 2 (r*(2*k+1)+1)) bottom.val.pack.layout :=
  (W.bundle position copies z).castLayout installed.symm

/-- The physical sewn layout on this particular public computation history.
It retains the actual cable-row ordering and saved frame data. -/
noncomputable abbrev network (q : (packHistory bottom M.epoch T).Index) :=
  enrichedSewnLayout (SewnTape.wiring p fit free pins) axes gridDepth order position count M bottom installed q

/-- All true private parameters, unary uses and gadget positions read on
the public state's actual sewn network. -/
noncomputable def tags (q : (packHistory bottom M.epoch T).Index)
    (z : Fin ((EnrichedOuter.fan S)^T) → Fin copies → W.Hidden position) :
    Tracked (Port (EnrichedOuter.fan S) (Fin copies × Unit) T) (PairedParameters k s) Gadget
      (Nat.clog 2 (r*(2*k+1)+1)) (network p fit position free count M bottom installed q) :=
  enrichedSewnTerm (SewnTape.wiring p fit free pins) axes gridDepth order position count M bottom installed
    y hy pos (base p fit W position bottom installed) hg q z

/-- The full sum over the compiler's enriched histories, including every
field assignment and both copies of the original private cable coordinates. -/
theorem substituted_eq (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (pin : Fin pins → Bool) (bank : Ports (fun _ : FreeBlock R (tileCount axes gridDepth) =>
      inputBlockWidth r (k+1) axes gridDepth))
    (delivered : ∀ z, let a := freeLane hg (gridRoom (SewnTape.wiring p fit free pins) Fintype.card_pos) z
      bank a.1 a.2 = freeBits (SewnTape.wiring p fit free pins) pin z) :
    substituted E k s (SewnTape.wiring p fit free pins).slot pin = ∑ q : (packHistory bottom M.epoch T).Index,
      ∑ z : Fin ((EnrichedOuter.fan S)^T) → Fin copies → W.Hidden position,
        ((tags p fit W position free count M bottom installed y hy pos hg q z).valued values).tensor bank := by
  have eqv := W.tape_groups count p fit position values free pin
  refine eqv.trans (Eq.trans ?_ (sum_enriched_sewn (SewnTape.wiring p fit free pins)
    axes gridDepth order position count M bottom installed y hy pos (base p fit W position bottom installed)
    values lookup hg pin bank delivered))
  apply Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _))
  intro ext _
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _))
  intro z _
  exact (Tracked.castLayout_tensor installed.symm (W.bundle position copies z) values _).symm

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
