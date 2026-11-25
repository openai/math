import OAI.Computability.BorderVNP.CubePhysicalOperandLedger
import OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun

/-! # The native allocated subtotal program serializes the physical path's monomial data

The native common prefix is expressed using current physical owners. After each local
row is checked, its column totals supply the original mathematical parameter powers and
gadget multiplicities at the exact little-endian addresses used by the residue reader.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyRAM
open DiagonalTallyMaterialize RoutingISA
open DiagonalResidueRAM (word)
open scoped BigOperators Classical

variable {n d blocks b h K s D B T H U w : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable {N : Network D P bits} {cell : N.Site → Cell}
variable (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (tags : N.Tables (Entry (Fin H) (Fin U)))
    (x : Ports bits) (pos : Packet n d blocks → TableEntry n b h K s → Fin U)
    (words : PowerWords (Fin T) (Fin H) (Fin U) B N tags)
    (label : Cell → Label (n+1) d) (team : Fin d → Fin T)
    (a : Path N cell n d blocks b h K s) (t : Fin T)
    (o : Orders tags words label team a t) (uses : PowerSlot (Fin T) (Fin H) B → UseRead)
    (cells : ∀ c : Cell, CellRead {v : N.Site // cell v = c} U)
    (packets : Packet n d blocks × Vertex (n+1) → PacketRead)

/-- Actual RAM execution from the operand directory and physical broadcast. The low-to-high
word bits at the end are the totals of the physical path tally for this same assignment.
This remains valid when the selected gadget scalar is zero in the ambient field. -/
theorem allocate_path_tallies (arena : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (state : Bank w) (mem : Memory w) (ptr : ℕ) (hT : arena.teams = T) (dim : arena.dim = H+U)
    (own : arena.team = t.val)
    (useBit : ∀ i, (uses i).bit = words.localUse (pathEdges slot a) (fun _ p => x p.val) i.1 i.2.1 i.2.2)
    (siteID : ∀ c (v : {v : N.Site // cell v = c}) g,
      (((cells c).observed v).filterMap Prod.snd).count g.val =
        (counters (tags v.val (pathEdges slot a v.val) (fun p => x p.val))).2 g) :
    ∀ os : List Operand, (os.map Operand.pair).Perm
      ((operands tags pos words label team a t o uses cells packets).map Operand.pair) →
    let rows := fun (i : Fin arena.teams) (j : Fin arena.dim) =>
      physicalRow slot tags x pos words label team a (Fin.cast hT i) (Fin.cast dim j)
    arena.seed pub mem ptr → arena.Fits w (pub 0).val → (pub 0).val+101 < 2^w →
    supplied mem arena.fresh ptr os →
    (∀ q, operandReads ptr os q → outsidePointers (pub 0).val q) →
    (∀ q, arena.raw≤q → q<arena.raw+(arena.teams*arena.dim)*arena.width → outsidePointers (pub 0).val q) →
    arena.count = o.nUse + o.nCell*U + o.nVertex →
    DiagonalTallyBits.WordsAt mem arena.raw (broadcast arena.width rows) →
    (∀ i c, rows i c < 2^arena.width) → (∀ c, ∑ i, rows i c < 2^w) →
    ∃ es z mz, Runs pub mac allocateAndEvaluate state mem es z mz ∧
      traceCost es ≤ allocateTallies.slots + arena.work w os ∧
      (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0) ∧
      ∀ c : Fin (H+U), ∀ j<w, mz ((arena.bitFrame w).dst+(c.val*w+j)) =
        word w (((∑ i : Fin T, tallyRow (pathTally slot tags x pos words label team a) i c).testBit j).toNat) := by
  intro os perm rows seed fit dir ops sep raw count bits rowFit sumFit
  have localCounts (c : Fin arena.dim) : arena.localRow os c.val = rows ⟨arena.team,fit.team⟩ c := by
    have castTeam : Fin.cast hT ⟨arena.team,fit.team⟩ = t := Fin.ext own
    unfold rows
    rw [castTeam]
    exact (increment_pair_perm perm arena.frame.localBase c.val).trans
      (increment_eq_row slot tags x pos words label team a t o uses cells packets arena.frame.localBase
        (Fin.cast dim c) useBit siteID)
  obtain ⟨es,z,mz,run,cost,good,result⟩ := allocateAndEvaluate_natural_runs arena pub mac state mem os ptr rows
    seed fit dir ops sep raw ((by simpa only [List.length_map] using perm.length_eq : os.length =
      (operands tags pos words label team a t o uses cells packets).length).trans
      ((operands_length tags pos words label team a t o uses cells packets).trans count.symm))
    (fun op hm => by
      obtain ⟨other,ho,eq⟩ := List.mem_map.mp (perm.mem_iff.mp (List.mem_map.mpr ⟨op,hm,rfl⟩))
      rw [←eq,dim]
      exact operands_coordinates tags pos words label team a t o uses cells packets other ho)
    bits localCounts rowFit sumFit
  refine ⟨es,z,mz,run,cost,good,fun c j hj => ?_⟩
  have value := result (Fin.cast dim.symm c) j hj
  have eq : (∑ i, rows i (Fin.cast dim.symm c)) =
      ∑ i : Fin T, tallyRow (pathTally slot tags x pos words label team a) i c := by
    change (∑ i, physicalRow slot tags x pos words label team a ((finCongr hT) i) (Fin.cast dim (Fin.cast dim.symm c))) = _
    rw [Fin.cast_cast,Fin.cast_eq_self,(finCongr hT).sum_comp (fun i => physicalRow slot tags x pos words label team a i c),
      sum_physicalRow]
  exact value.trans (congrArg (fun z : ℕ => word w (z.testBit j).toNat) eq)

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
