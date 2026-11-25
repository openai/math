import OAI.Computability.BorderVNP.FiniteDiagonalCubeRawGrid
import OAI.Computability.BorderVNP.PackedInheritedMergedEnds

/-! # The true raw field weight as the product over the owned private cells

Once the checked shared and local packet payloads are fixed, each host cell
uses only its own flat private vector. Its incoming lanes read its own end
of each delivered crossing, together with its actual supplied public ports.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldSiteDirectory

open Crossing Packing Packing.Inherited Packing.CellAddresses BorderVNP.Cube
open Cube.Physical Cube.Physical.NativeAssignments Cube.Scatter.Assignment
open scoped BigOperators Classical

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 800000

variable {D m teams : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] {T : N.Tables F} (S : FieldSiteDirectory N T) (L : FieldPacketPlan N F)
  (siteID : N.Site ↪ Fin m)
  (owners : (Packet L.dimension L.alphabet L.blocks → Selector L.dimension L.alternatives L.copies) →
    Fin L.alphabet → Fin teams)

private abbrev Route := Routed (b := L.bitWidth) (s := L.supply) owners

/-- The independently routed bits, which have the same values for every
choice of private inside wires and sparse work tapes. -/
def cubeInputs (q : Route L owners) :
    CubeTerm (Packet L.dimension L.alphabet L.blocks) (SingleSlot L.dimension L.alphabet L.blocks (L.copies*L.bitWidth))
      L.dimension L.bitWidth L.copies L.alternatives L.supply D :=
  let u := q.1
  let z := (payloadEquiv (D := D) (b := L.bitWidth) (s := L.supply) u).symm
    (lookup q.2)
  (z.1,z.2.1,⟨u,z.2.2⟩)

/-- Source and destination end values read by the true incidence serializer. -/
def routedEnds (q : Route L owners) (side : Bool) (bit : LiveBit N L.cell) : Bool :=
  let z := cubeInputs L owners q
  readEnd z.1 z.2.1 side (L.slot bit)

/-- A true raw assignment identifies its original sparse work words and
originally shared local wires without reconstructing any other cell. -/
theorem routed_read (q : Route L owners) (raw : S.FlatWork L) :
    S.routedRawEquiv L siteID owners (q,raw) =
      (S.workOfFlat L siteID raw,
        (Placement.insideOfRaw N L.cell S.edgeID S.site raw,cubeInputs L owners q)) := rfl

/-- The factor of one physical host cell at its flat vector and delivered ends. -/
noncomputable def rawCell (x : Ports bits) (q : Route L owners) (c : L.Cell)
    (g : Fin (externalBase N L.cell c S.workWidth) → Bool) : F :=
  let inner := privateWires N L.cell S.workWidth c g
  let incoming := Placement.endSupply N L.cell c S.edgeID S.portID x (routedEnds L owners q)
  let works := siteWords N L.cell c siteID S.workWidth (privateStaging N L.cell S.workWidth c g)
  ∏ v : {v : N.Site // L.cell v = c},
    ((S.site v.val).observe (Inherited.bits (works v)
      ((Placement.canonical N L.cell c S.edgeID S.portID v inner incoming) ∘ Fin.cast (S.incoming v.val)))).elim 0
        (fieldWeight S.values)

/-- Unused slot ends are checked exactly in the locations opened by the
selected packet layout. -/
def pinsPass (q : Route L owners) : Prop :=
  let z := cubeInputs L owners q
  ∀ a ∉ Set.range L.slot, readEnd z.1 z.2.1 false a = false ∧ readEnd z.1 z.2.1 true a = false

/-- At a fixed public packet and private routing choice, the full sparse
host factorizes into independent physical owned-cell operands and the cube scalars. -/
theorem pathValue_eq_cells (x : Ports bits) (q : Route L owners) (raw : S.FlatWork L) :
    let a := S.routedRawEquiv L siteID owners (q,raw)
    S.pathValue L x a.2 a.1 =
      (if pinsPass L owners q then ∏ c, S.rawCell L siteID owners x q c (raw c) else 0) *
        cubeTermWeight L.table (fun _ _ => 1) (cubeInputs L owners q) := by
  intro a
  dsimp only [a]
  rw [S.routed_read L siteID owners q raw]
  unfold pathValue hostValue
  congr 1
  dsimp only
  unfold pinsPass
  split_ifs with ok
  · rw [← Fintype.prod_fiberwise L.cell (fun v => S.siteValue L x
      (Placement.insideOfRaw N L.cell S.edgeID S.site raw,cubeInputs L owners q) v (S.workOfFlat L siteID raw v))]
    apply Finset.prod_congr rfl
    intro c _
    unfold rawCell
    apply Finset.prod_congr (Finset.ext fun _ => by simp)
    intro v _
    have word := Placement.canonical_ends N L.cell c S.edgeID S.portID S.site x (routedEnds L owners q) raw v
    have work := S.workOfFlat_cell L siteID raw c v
    unfold siteValue input
    rw [work]
    exact congrArg (fun f => ((S.site v.val).observe (Inherited.bits
      (siteWords N L.cell c siteID S.workWidth (privateStaging N L.cell S.workWidth c (raw c)) v)
      (f ∘ Fin.cast (S.incoming v.val)))).elim 0 (fieldWeight S.values)) word.symm
  · rfl

/-- The cells' native private computations can sum independently once
their received payloads have been fixed. -/
theorem sum_flat_cells (x : Ports bits) (q : Route L owners) :
    (∑ raw : S.FlatWork L, let a := S.routedRawEquiv L siteID owners (q,raw)
      S.pathValue L x a.2 a.1) =
      (if pinsPass L owners q then ∏ c, ∑ g, S.rawCell L siteID owners x q c g else 0) *
        cubeTermWeight L.table (fun _ _ => 1) (cubeInputs L owners q) := by
  simp_rw [S.pathValue_eq_cells L siteID owners x q]
  rw [← Finset.sum_mul]
  by_cases ok : pinsPass L owners q
  · simp only [ite_eq_left ok]
    rw [Fintype.prod_sum]
  · simp only [ite_eq_right ok,Finset.sum_const_zero]

end FiniteDiagonal.FieldSiteDirectory

end BorderVNP
end Computability
end OAI
