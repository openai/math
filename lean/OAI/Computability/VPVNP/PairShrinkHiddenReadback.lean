import OAI.Computability.VPVNP.PairShrinkHiddenParser
import OAI.Computability.VPVNP.PairShrinkHiddenStep
import OAI.Computability.VPVNP.PairNodeChildPackets

/-!
# Reading both map columns after the complete hidden-field scan

The final private memory of the native shrinking guess worker is a fold of
field stores. Distinct dense identifiers keep all of these fields resident
through the end of the scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkHiddenSlots

open BurstRAM ShrinkHiddenGuess NodeArguments Compression Compression.ShrinkMotif NetworkKernel
open scoped Fin.CommRing Classical

variable {w : ℕ}

/-- Read one member of the complete native scan's private-memory update. -/
theorem storeRows_read (base stride : ℕ) (es : List Row) (old : Word w → Word w)
    (fits : ∀ r ∈ es, r.2.length ≤ stride ∧ base + r.1 * stride + r.2.length ≤ 2 ^ w)
    (distinct : (es.map Prod.fst).Nodup) (r : Row) (hr : r ∈ es) (i : Fin r.2.length) :
    storeRows base stride es old ((base + r.1 * stride + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w r.2[i.val] := by
  let arena : Arena := ⟨base,stride⟩
  let packet : Row → Packet := fun e => ⟨e.1,e.2⟩
  have packetFit : ∀ q ∈ es.map packet, q.Fits arena w 0 := by
    intro q hq
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hq
    exact ⟨Nat.zero_le _, fits e he⟩
  have packetDistinct : ((es.map packet).map Packet.node).Nodup := by
    simpa only [List.map_map, Function.comp_def, packet] using distinct
  have stored := writePackets_children arena _ (DFS.scratch 0 old) packetFit packetDistinct (packet r)
    (List.mem_map_of_mem hr) i
  rw [← ChildScan.scratch_storePackets] at stored
  change rawScratch (DFS.scratch 0 (ChildScan.storePackets arena (es.map packet) old))
      ((base + r.1 * stride + i.val : ℕ) : Word w) = PrivateFields.bitValue w r.2[i.val] at stored
  simpa only [rawScratch, dite_true, Nat.zero_le, DFS.scratch, ChildScan.storePackets, storeRows, List.foldl_map, packet, arena, Arena.base]
    using stored

variable {a g : ℕ} (X : State a (packingLaneBits a g)) (base stride : ℕ)
variable (layout : Bool) (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)

/-- The allocation of one private slot per dense identifier bounds every
field store in each site's restricted row. -/
theorem rows_fit (v : (X.Base × BitWord (packingTagBits (2 ^ a))) × BitWord g)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout) v)
    (size : ∀ m t, widths m (!layout,t) ≤ stride)
    (cap : base + (CompressorRecords.ShrinkHistoryRows.hiddenOrder X).length * stride ≤ 2 ^ w) :
    ∀ r ∈ rows X layout widths v h, r.2.length ≤ stride ∧ base + r.1 * stride + r.2.length ≤ 2 ^ w := by
  intro r hr
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
  let o := CompressorRecords.ShrinkHistoryRows.residents (CompressorRecords.ShrinkHistoryRows.hiddenOrder X)
    (X.packingData.shrinkInternalOwner layout) v
  let e := (o.entries j).val
  change (List.ofFn (RAMSerialization.wordBits _ (h e _))).length ≤ stride ∧
    base + id X e * stride + (List.ofFn (RAMSerialization.wordBits _ (h e _))).length ≤ 2 ^ w
  rw [List.length_ofFn]
  have hs := size e.1 e.2
  have hi : id X e < (CompressorRecords.ShrinkHistoryRows.hiddenOrder X).length :=
    ((CompressorRecords.ShrinkHistoryRows.hiddenOrder X).entries.symm e).isLt
  have step := Nat.mul_le_mul_right stride hi
  rw [Nat.succ_mul] at step
  exact ⟨hs, by omega⟩

/-- Every owned coordinate remains available after all rows have been written. -/
theorem resident_read (v : (X.Base × BitWord (packingTagBits (2 ^ a))) × BitWord g)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout) v)
    (old : Word w → Word w)
    (fits : ∀ r ∈ rows X layout widths v h, r.2.length ≤ stride ∧
      base + r.1 * stride + r.2.length ≤ 2 ^ w)
    (e : X.packingData.Motif × Fin 4) (hv : v = X.packingData.shrinkInternalOwner layout e)
    (i : Fin (widths e.1 (!layout,e.2))) :
    storeRows base stride (rows X layout widths v h) old
      ((address X base stride e + i.val : ℕ) : Word w) =
        PrivateFields.bitValue w (RAMSerialization.wordBits _ (h e hv) i) := by
  let bits := RAMSerialization.wordBits _ (h e hv)
  have stored := storeRows_read base stride _ old fits (rows_nodup X layout widths v h)
    (id X e, List.ofFn bits) (mem_rows X layout widths v h e hv) ⟨i.val, by simp [bits]⟩
  simpa only [address, List.getElem_ofFn, bits] using stored

variable {b pad : ℕ} (subdiv : Fin 4 → ℕ)
variable {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
variable (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad) (hpos : ∀ t, 0 < subdiv t)
local notation "Y" => X.packingData.shrinkOutput layout subdiv (fun m t ↦ widths m (layout,t)) I

/-- The same native store scan supplies the bit to either endpoint of the
absorbed edge, evaluated on the local party's independent half-wires. -/
theorem storeRows_mapColumn (m : X.packingData.Motif) (t : Fin 4) (dir : Bool)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout)
      (X.packingData.shrinkInternalOwner layout (m,t)))
    (z : (Y).Half (X.packingData.shrinkInternalOwner layout (m,t))) (old : Word w → Word w)
    (fits : ∀ r ∈ rows X layout widths _ h, r.2.length ≤ stride ∧ base + r.1 * stride + r.2.length ≤ 2 ^ w)
    (i : Fin (widths m (!layout,t))) :
    storeRows base stride (rows X layout widths _ h) old
      ((address X base stride (m,t) + i.val : ℕ) : Word w) =
        PrivateFields.bitValue w (RAMSerialization.wordBits _
          (mapColumn X layout subdiv widths I hpos m t dir h z) i) := by
  rw [mapColumn_eq]
  exact resident_read X base stride layout widths _ h old fits (m,t) rfl i

end PairSimulation.ShrinkHiddenSlots

end

end VPVNP
end Computability
end OAI
