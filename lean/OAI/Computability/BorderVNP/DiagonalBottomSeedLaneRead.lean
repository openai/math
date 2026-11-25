import OAI.Computability.BorderVNP.DiagonalBottomBundlePowerRead
import OAI.Computability.BorderVNP.PackedGridSeedValue
import OAI.Computability.BorderVNP.PackedBottomWiredSite

/-! # Recovering original fine input bits from the actual retained public input

The supplied region at a bottom site reads copy-major cable slices and the
grouped lane of every attached fine port. The transport from the canonical
public grid to the routed verifier preserves these individual coordinates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.PowerInput

open Crossing

/-- Transport of a full input along an equality of layouts preserves the
assignment and the exterior values, up to their induced type equalities. -/
theorem cast_coordinates {D : ℕ} {P : Type} {bits : P → ℕ} {N M : Network D P bits}
    (h : N=M) (a : PowerInput M) :
    HEq (Eq.mpr (congrArg PowerInput h) a).edges a.edges ∧
      (Eq.mpr (congrArg PowerInput h) a).ports = a.ports := by
  subst M
  exact ⟨HEq.rfl,rfl⟩

end Diagonal.CellEntries.PowerInput

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse CellAddresses BottomGridBank BottomReports Inherited GridBoxes
open GridPlacement Cover TeamContraction ParseBatch ParseBatchVerifier Prewire
open VPVNP VPVNP.ParseGrammar Diagonal.CellEntries Diagonal.ExternalSew
open scoped Classical
set_option maxHeartbeats 1800000

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- The equality used by the routed seed's actual deck-grid table. -/
noncomputable local instance birthGridEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "Tile₀" => (Fin q → Deck (depth+2))
local notation "tiles" => GridHosts.tileCount q depth
local notation "lane₀" => GridHosts.wiredLane G tiles Fintype.card_pos
local notation "width₀" => (fun _ : Fin tiles => GridHosts.inputBlockWidth r n q depth)
local notation "net₀" => W.routedFine position
local notation "owner₀" => cell position W.route
local notation "packing₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "grouped₀" => W.seedGrouped position
local notation "wired₀" => wiredGrid G q depth order position

variable {copies : ℕ} (a : PowerInput ((wiredGrid G q depth order position).groupedRepeat
      (fun _ : Fin (Fintype.card (Fin q → Deck (depth+2))) => GridHosts.inputBlockWidth r n q depth) order copies)) (i : Fin copies)

/-- The true bottom-copy pullback gives the indicated slice of every old grid cable. -/
theorem seedCopyInput_edge (e : (W.seedGrid position).Edge) (j : Fin ((W.seedGrid position).width e)) :
    (W.seedCopyInput position a i).edges e j = a.edges e (finProdFinEquiv (i,j)) := by
  let old := PowerInput.groupedCopy (N := wired₀) width₀ lane₀ order i a
  have he : (W.seedCopyInput position a i).edges = old.edges :=
    eq_of_heq (PowerInput.cast_coordinates (W.seedGrid_eq position) old).1
  exact congrFun (congrFun he e) j

/-- The old fine exterior port recovers its numbered bit in the original
processor's grouped word, inside the selected copy. -/
theorem seedCopyInput_port (p : Fin r × Fin (publicWidth G)) (j : Fin 1) :
    (W.seedCopyInput position a i).ports p j =
      a.ports (lane₀ p).1 (finProdFinEquiv (i,(lane₀ p).2)) := by
  let old := PowerInput.groupedCopy (N := wired₀) width₀ lane₀ order i a
  exact congrFun (congrFun (PowerInput.cast_coordinates (W.seedGrid_eq position) old).2 p) j

variable {ne np qe qa : ℕ} (edges : (W.routedFine position).Edge ↪ Fin ne) (ports : (Fin r × Fin (publicWidth G)) ↪ Fin np)
    (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe) (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2))

/-- The native compact fine-supply vector, read from its original repeated
public site input, equals all of the true fine verifier's exposed wires and ports. -/
theorem seedCopyInput_fine :
    scalarFine net₀ owner₀ position packing₀ width₀ order lane₀ (W.seedLane_aligned position)
      edges ports channels groups c copies
      (inputWords (BottomRepeat.wide grouped₀ copies) channels groups c (fun e => a.edges e.val) (fun p => a.ports p.val)) i =
    (suppliedWords net₀ owner₀ c edges ports).symm (publicWords owner₀ position packing₀ c
      (fun e => (W.seedCopyInput position a i).edges e.val) (fun p => (W.seedCopyInput position a i).ports p.val)) := by
  have h := copy_supplied_pull net₀ owner₀ position packing₀ width₀ order lane₀ (W.seedLane_aligned position)
    edges ports channels groups c copies i (fun e => a.edges e.val) (fun p => a.ports p.val)
  refine h.trans (congrArg (suppliedWords net₀ owner₀ c edges ports).symm ?_)
  apply congrArg₂ (publicWords owner₀ position packing₀ c)
  · funext e j
    exact (W.seedCopyInput_edge position a i e.val j).symm
  · funext p j
    exact (W.seedCopyInput_port position a i p.val j).symm

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
