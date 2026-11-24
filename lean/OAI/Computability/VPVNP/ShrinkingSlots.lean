import OAI.Computability.VPVNP.PackingLanes
import OAI.Computability.VPVNP.PackingPreimages
import OAI.Computability.VPVNP.RegularizedMotifs
import OAI.Computability.VPVNP.SlotIdentifierOrder
import Mathlib.Algebra.Module.Pi

/-!
# The shrinking step's slot construction

Lemma C.1 of *VP and VNP differ over every field* for a directed input
slot graph with arbitrary binary displacements. `dyadic_slot_packing`
counts the thick wires, CD demands and placed role incidences on the actual
input. `dyadicSurvivingSlots` constructs the indexed, regularized output
lift. The lane-zero labels preserve parallel edges and subdivisions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open SurvivingSlots PackingData

variable {V : Type*} [Fintype V] [DecidableEq V] {a g : ℕ}
variable (G : LiftedSlots V (2 ^ a) (BitWord (packingLaneBits a g)))

/-- The multiplicities and distinct-endpoint assertions of Lemma C.1, for
the construction obtained directly from the given input graph. -/
theorem dyadic_slot_packing :
    let P := dyadicPacking G
    let d := 2 ^ a
    let K := 2 ^ (2 * d + 1) * d
    let Q := 3 * K / 4
    Fintype.card (V × BitWord (packingLaneBits a g)) =
        K * Fintype.card (Site V (BitWord (packingTagBits d)) (BitWord g)) ∧
      (∀ b, Fintype.card {e // e.1 = b ∧ P.thick (sourcePosition e) ∧
        P.thick (sourcePosition (P.actual e))} = K / 4) ∧
      (∀ b, Fintype.card {m : P.Motif // P.bundle m = b} = Q) ∧
      (∀ layout s, Fintype.card {x // P.placement layout x = s} = K) ∧
      (∀ layout m, packedBase (P.roleA m) ≠ packedBase (P.roleB m) ∧
        packedBase (P.roleA m) ≠ packedBase (P.roleD layout m) ∧
        packedBase (P.roleB m) ≠ packedBase (P.roleD layout m)) ∧
      ∀ layout role s, Fintype.card {m : P.Motif // P.survivingRole layout role m = s} = d * Q := by
  let P := dyadicPacking G
  have hd : 0 < 2 ^ a := Nat.two_pow_pos _
  have hc : 2 ≤ 2 * 2 ^ a + 1 := by omega
  refine ⟨packing_position_count V a g, P.card_thick_bundle hc, P.card_motifs_bundle hc,
    P.card_placement (by omega), P.distinct_roleBases (dyadicPacking_validTags G),
    fun layout role s ↦ ?_⟩
  cases role with
  | a => exact P.card_roleA hc s
  | b => exact P.card_roleB hc s
  | d => exact P.card_roleD hc layout s

private def dyadicSlotIndexing (P : DyadicPackingData V a g)
    (hφ : P.slots.ValidTagOffsets P.tagShift P.offset) (layout : Bool) (subdiv : Fin 4 → ℕ)
    [LinearOrder (Id P.BaseMotif subdiv)] {d' : ℕ}
    (hd' : survivingDegree (2 ^ a) (2 * 2 ^ a + 1) subdiv ≤ d') :=
  let j := packingTagBits (2 ^ a)
  have hd : 0 < 2 ^ a := Nat.two_pow_pos _
  have hc : 2 ≤ 2 * 2 ^ a + 1 := by omega
  have hj : 0 < j := Nat.succ_pos _
  P.regularizedSlotIndexing hc hφ layout subdiv hd' (bitWordFinEquiv j)
    (Nat.one_lt_two_pow hj.ne')

/-- Number the actual surviving arcs by their lane-zero motif IDs, padding
with dummy arcs to any admissible output degree `d'`. The resulting graph
has packed bases `(old vertex, tag)` and the original remaining lane. -/
noncomputable def dyadicSurvivingSlots (layout : Bool) (subdiv : Fin 4 → ℕ)
    [LinearOrder (Id (dyadicPacking G).BaseMotif subdiv)] {d' : ℕ}
    (hd' : survivingDegree (2 ^ a) (2 * 2 ^ a + 1) subdiv ≤ d') :=
  dyadicSlotIndexing (dyadicPacking G) (dyadicPacking_validTags G) layout subdiv hd'

/-- The supplied vertex numbering determines both the greedy scans and the
integer keys for sorting the local incoming and outgoing incidence lists. -/
def orderedDyadicSurvivingSlots {N : ℕ} (vertices : V ≃ Fin N) (layout : Bool)
    (subdiv : Fin 4 → ℕ) {d' : ℕ} (hd' : survivingDegree (2 ^ a) (2 * 2 ^ a + 1) subdiv ≤ d') :=
  let P := orderedDyadicPacking G vertices
  letI := P.slotIdentifierOrder vertices (bitWordFinEquiv (packingTagBits (2 ^ a))) subdiv
  dyadicSlotIndexing P (orderedDyadicPacking_validTags G vertices) layout subdiv hd'

end Compression

end VPVNP
end Computability
end OAI
