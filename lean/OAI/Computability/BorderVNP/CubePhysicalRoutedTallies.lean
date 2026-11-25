import OAI.Computability.BorderVNP.CubePhysicalTally
import OAI.Computability.BorderVNP.DiagonalTallyPacketRecipe
import OAI.Computability.BorderVNP.DiagonalTallyRAMValues

/-! # Parameter rows by current physical owner and cube lookup rows by actual table ID

The binary use slots of the substituted polynomial are indexed by their original
batch. The same slots are processed in RAM by the present owner of their current
host cell. Summing the physical natural-number rows reindexes every slot once.
The scalar rows are already indexed by physical ownership in the mathematical tally.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal Diagonal.CellEntries
open scoped BigOperators Classical

set_option synthInstance.maxSize 768

variable {n d blocks b h K s D B T H U : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable {N : Network D P bits} {cell : N.Site → Cell}
variable (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
variable (tags : N.Tables (Entry (Fin H) (Fin U))) (x : Ports bits)
variable (pos : Packet n d blocks → TableEntry n b h K s → Fin U)
variable (words : PowerWords (Fin T) (Fin H) (Fin U) B N tags)
variable (label : Cell → Label (n+1) d) (team : Fin d → Fin T)
variable (a : Path N cell n d blocks b h K s)

/-- Current processor team that reads the use bit of one weighted unary occurrence. -/
def routedPowerOwner (i : PowerSlot (Fin T) (Fin H) B) : Fin T :=
  pathOwner label team a (.inl (words.site i))

/-- Increment of a natural parameter subtotal from this actual original power slot. -/
noncomputable def routedPower (i : PowerSlot (Fin T) (Fin H) B) (p : Fin H) : ℕ :=
  slotPower i (words.localUse (pathEdges slot a) (fun _ j => x j.val) i.1 i.2.1 i.2.2) p

/-- The owner's parameter subtotal is a natural sum over the occurrences in its
current host cells, including repeated powers with the same parameter and place. -/
noncomputable def routedParameterRow (t : Fin T) (p : Fin H) : ℕ :=
  ∑ i : {i : PowerSlot (Fin T) (Fin H) B // routedPowerOwner tags words label team a i = t},
    routedPower slot tags x words a i.val p

omit [Fintype Cell] in
/-- All parameter rows together recover the exponent of the original batch-indexed
tally. Several batches' powers at a given place can have the same physical owner. -/
theorem sum_routedParameterRow (p : Fin H) :
    (∑ t, routedParameterRow slot tags x words label team a t p) =
      (pathTally slot tags x pos words label team a).exponents p := by
  unfold routedParameterRow
  rw [Fintype.sum_fiberwise (routedPowerOwner tags words label team a) (fun i => routedPower slot tags x words a i p)]
  simp only [PowerSlot,Fintype.sum_prod_type,routedPower,slotPower,Finsupp.single_apply,
    pathTally,PowerWords.localTally,Diagonal.Tally.exponents,Diagonal.batchExponent,Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q = p
  · subst q; simp
  · simp [hq]

/-- ID of the selected scalar entry computed by the physical packet lookup, using
the actual selector, vertex, demand-end words and supply-edge assignment. -/
def pathPacketID (pv : Packet n d blocks × Vertex (n+1)) : Fin U :=
  pos pv.1 (Cube.Tally.packetEntry D b s (a.2.2.2.1 pv.1) pv.2 (a.2.2.1 pv.1) (a.2.2.2.2 pv.1))

omit [Fintype Cell] [DecidableEq Cell] in
/-- The packet contribution in a mathematical physical path uses exactly the ID
read by the native packet lookup, even when its field value is zero. -/
theorem pathExtra_eq_lookup (pv : Packet n d blocks × Vertex (n+1)) :
    pathExtra (Param := Fin H) pos a pv = gadget (pathPacketID pos a pv) := rfl

/-- Rewriting a sum over a routed owner fiber as a masked sum on the full
finite population preserves each occurrence, including ties in the owner map. -/
theorem sum_owner_fiber {A I : Type*} [Fintype A] [DecidableEq I]
    (owner : A → I) (t : I) (f : A → ℕ) :
    (∑ i : {i : A // owner i = t}, f i.val) = ∑ i, if owner i = t then f i else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => owner i = t)) (by simp) f,
    Finset.sum_filter]

/-- The owner of all original site factors placed in this actual host cell. -/
def pathCellOwner (c : Cell) : Fin T :=
  team (label c (chosen b s a.2.2.2.1))

/-- The original site-tag multiplicities in a single host cell, without the additional
cube factors. This is the count the cell macro verifies before the outer tally reads it. -/
noncomputable def pathCellCounts (c : Cell) (g : Fin U) : ℕ :=
  ∑ v : {v : N.Site // cell v = c},
    (counters (tags v.val (pathEdges slot a v.val) (fun p => x p.val))).2 g

/-- The mathematical gadget row is the sum of the routed host-cell counts and one
actual lookup ID from each routed cube vertex. This formula includes field-zero entries. -/
theorem pathTally_counts_eq_cells_packets (t : Fin T) (g : Fin U) :
    (pathTally slot tags x pos words label team a).counts t g =
      (∑ c : {c : Cell // pathCellOwner label team a c = t}, pathCellCounts slot tags x a c.val g) +
      ∑ pv : {pv : Packet n d blocks × Vertex (n+1) // pathOwner label team a (.inr pv) = t},
        if pathPacketID pos a pv.val = g then 1 else 0 := by
  let siteCount (v : N.Site) := (counters (tags v (pathEdges slot a v) (fun p => x p.val))).2 g
  have sites : (∑ c : {c : Cell // pathCellOwner label team a c = t}, pathCellCounts slot tags x a c.val g) =
      ∑ v : N.Site, if pathCellOwner label team a (cell v) = t then siteCount v else 0 := by
    rw [sum_owner_fiber (pathCellOwner label team a) t (fun c => pathCellCounts slot tags x a c g),
      ←Fintype.sum_fiberwise cell (fun v => if pathCellOwner label team a (cell v) = t then siteCount v else 0)]
    apply Finset.sum_congr rfl
    intro c _
    have same (v : {v : N.Site // cell v = c}) : cell v.val = c := v.property
    by_cases hc : pathCellOwner label team a c = t
    · simp only [hc,ite_true,pathCellCounts,same,siteCount]
    · simp [hc,same]
  rw [sites,sum_owner_fiber (fun pv => pathOwner label team a (.inr pv)) t
    (fun pv => if pathPacketID pos a pv = g then 1 else 0)]
  simp only [pathTally,PowerWords.localTally]
  let W (v : N.Site ⊕ (Packet n d blocks × Vertex (n+1))) :=
    (counters (v.elim (fun z => tags z (pathEdges slot a z) (fun p => x p.val)) (pathExtra pos a))).2 g
  have forget (enum : Fintype {v // pathOwner label team a v = t}) :
      (∑ v ∈ @Finset.univ _ enum, W v.val) = ∑ v, if pathOwner label team a v = t then W v else 0 := by
    have eq := sum_owner_fiber (pathOwner label team a) t W
    exact (Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim enum _)) (fun _ _ => rfl)).trans eq
  refine (forget _).trans ?_
  rw [Fintype.sum_sum_type]
  apply congrArg₂ (·+·) rfl
  apply Finset.sum_congr rfl
  intro pv _
  simp [W,pathExtra_eq_lookup,gadget,Finsupp.single_apply]

/-- Natural rows used by the RAM subtotal broadcast: the original unary choices
grouped by their current owners, followed by all host and cube gadget counts. -/
noncomputable def physicalRow (t : Fin T) : Fin (H+U) → ℕ :=
  Fin.append (routedParameterRow slot tags x words label team a t)
    ((pathTally slot tags x pos words label team a).counts t)

omit [Fintype Cell] in
/-- The summed natural subtotal words from all physical teams are the parameter
exponents and scalar counts used by the residue entry computation. -/
theorem sum_physicalRow (j : Fin (H+U)) :
    (∑ t, physicalRow slot tags x pos words label team a t j) =
      ∑ t, DiagonalTallyRAM.tallyRow (pathTally slot tags x pos words label team a) t j := by
  refine Fin.addCases ?_ ?_ j
  · intro p
    simp only [physicalRow,Fin.append_left]
    exact (sum_routedParameterRow slot tags x pos words label team a p).trans
      (DiagonalTallyRAM.tallyRow_parameter _ _).symm
  · intro g
    simp only [physicalRow,Fin.append_right,DiagonalTallyRAM.tallyRow]

end Cube.Physical

end BorderVNP
end Computability
end OAI
