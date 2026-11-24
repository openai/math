import OAI.Computability.VPVNP.CompressorRecordsDemandWidths
import OAI.Computability.VPVNP.CompressorShrinkDemandGather
import OAI.Computability.VPVNP.CompressorShrinkMotifOrder
import OAI.Computability.VPVNP.CompressorTermRecordScan

/-!
# Physical AB/CD demand inputs of a shrinking pass

The balanced AB pieces and the original CD widths are stored in distinct
rectangles. The paired gather visits their common bundle and rank. Its
two output cells form the exact input to the six-party term reader.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTermInputs

open Compression Compression.PackingData BurstRAM

variable {w : ℕ}

/-- The two rectangle heads and strides are the ones used by the prefix and
balanced-piece passes. The first word is the common number of CD ranks. -/
def operands (cdRows ab : Fin 5 → BurstRAM.Word w) (dense : BurstRAM.Word w) : Fin 6 → BurstRAM.Word w :=
  ![ab 0, ab 1, cdRows 1, ab 3, cdRows 2, dense]

section Packed

variable {V H T L : Type} {n d c : ℕ}
variable [AddCommGroup H] [AddCommGroup T] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype T] [Fintype L]
variable [DecidableEq V] [DecidableEq T] [DecidableEq L]
variable (P : PackingData V H T L d c) (site : Site V T L ≃ Fin n) (old : Arc V H T L d c → ℕ)
variable (cd : P.BundleNumbering)

/-- The dense scan order is the CD ordinal used at both AB endpoints.
Cell zero holds the balanced AB width and cell one the original CD width. -/
def Pairs (dense : BurstRAM.Word w) (mem : Memory w) : Prop :=
  ∀ m : P.Motif, let j := (ShrinkMotifOrder.number P cd site m).val
    (mem (dense.val+2*j)).val = P.abWidth cd old m ∧ (mem (dense.val+2*j+1)).val = old m.val

theorem gather (dd : P.ThickNumbering) (thick cdRows ab : Fin 5 → BurstRAM.Word w)
    (dense : BurstRAM.Word w) (mem : Memory w)
    (stored : DemandWidths.Stored P site old dd cd thick cdRows ab mem)
    (layout : ShrinkDemandGather.Layout (n*d) (pieceCount d c) (operands cdRows ab dense))
    {cap : ℕ} (hcap : ShrinkDemandGather.cost < cap) :
    ∃ rs, ShrinkDemandGather.Gathered (n*d) (pieceCount d c) (operands cdRows ab dense) cap mem rs ∧
      Pairs P site old cd dense (after mem (eventLog rs)) := by
  obtain ⟨rs,h⟩ := ShrinkDemandGather.gather layout mem hcap
  refine ⟨rs,h,fun m => ?_⟩
  let b := P.bundle m
  let x : P.MotifFiber b := ⟨m,rfl⟩
  let r := cd b x
  let j := BundleLists.portIndex site b
  have he := (cd b).symm_apply_apply x
  have hab := (congrArg Fin.val (h.readAB j.val j.isLt r.val r.isLt)).trans (stored.ab.widths b r)
  have hcd := (congrArg Fin.val (h.readCD j.val j.isLt r.val r.isLt)).trans (stored.cdWidths b r)
  change (after mem (eventLog rs) (dense.val+2*(ShrinkMotifOrder.number P cd site m).val)).val = _ ∧
    (after mem (eventLog rs) (dense.val+2*(ShrinkMotifOrder.number P cd site m).val+1)).val = _
  rw [ShrinkMotifOrder.number_val]
  rw [show (cd b).symm r = x from he] at hab hcd
  exact ⟨hab,hcd⟩

end Packed

/-- Read a dense array of pairs using the fixed two-coordinate order of the block. -/
private theorem pairInputs {m : ℕ} (b : Fin m → Bool → ℕ) (dense term : BurstRAM.Word w)
    (stride : ℕ) (wide : 10 ≤ stride) (sep : dense.val+m*2 ≤ term.val)
    (room : term.val+m*stride < 2^w) (mem : Memory w)
    (pairs : ∀ (j : Fin m), (mem (dense.val+2*j.val)).val = b j false ∧ (mem (dense.val+2*j.val+1)).val = b j true) :
    TermRecordScan.Inputs finTwoEquiv (TermRecordScan.strided m 2 8 w dense.val term.val 2 stride le_rfl wide sep room) b mem := by
  let rows := TermRecordScan.strided m 2 8 w dense.val term.val 2 stride le_rfl wide sep room
  intro j
  have hs : (rows.source j).val = dense.val+2*j.val := by
    have h := Nat.mul_le_mul_right 2 j.isLt
    rw [Nat.succ_mul] at h
    change (dense.val+j.val*2)%(2^w) = _
    rw [Nat.mod_eq_of_lt (by omega),Nat.mul_comm]
  funext e
  cases e with
  | false =>
    have h := DemandPreparation.demandAt_address finTwoEquiv (rows.source j) mem (rows.sourceFits j) (0 : Fin 2)
    exact h.trans (by change (mem ((rows.source j).val+0)).val = _; rw [hs,Nat.add_zero]; exact (pairs j).1)
  | true =>
    have h := DemandPreparation.demandAt_address finTwoEquiv (rows.source j) mem (rows.sourceFits j) (1 : Fin 2)
    exact h.trans (by change (mem ((rows.source j).val+1)).val = _; rw [hs]; exact (pairs j).2)

section State

variable {a g : ℕ} (X : State a (packingLaneBits a g))
open scoped Classical

/-- Number of CD motifs in the input state's packing data. -/
abbrev motifCount := Fintype.card X.packingData.Motif

/-- The two shrinking demand widths for the motif at a given dense physical ordinal. -/
noncomputable abbrev demand (j : Fin (motifCount X)) :=
  X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth (ShrinkMotifOrder.entries X j)

/-- The memory readback that identifies dense demand pairs with their actual motifs and packing
widths in this state. -/
noncomputable abbrev statePairs (dense : BurstRAM.Word w) (mem : Memory w) :=
  Pairs X.packingData (Shrink.packedIndex X.baseIndex) X.packingWidth X.shrinkNumber dense mem

/-- Term records have two headers and eight supply coordinates. A larger
stride leaves the padding available to the surrounding record directory. -/
def termRows (dense term : BurstRAM.Word w) (stride : ℕ) (wide : 10 ≤ stride)
    (sep : dense.val+motifCount X*2 ≤ term.val) (room : term.val+motifCount X*stride < 2^w) :=
  TermRecordScan.strided (motifCount X) 2 8 w dense.val term.val 2 stride le_rfl wide sep room

set_option maxHeartbeats 1200000 in
theorem inputs (dense term : BurstRAM.Word w) (stride : ℕ) (wide : 10 ≤ stride)
    (sep : dense.val+motifCount X*2 ≤ term.val) (room : term.val+motifCount X*stride < 2^w)
    (mem : Memory w) (pairs : statePairs X dense mem) :
    TermRecordScan.Inputs finTwoEquiv (termRows X dense term stride wide sep room) (demand X) mem := by
  apply pairInputs (demand X) dense term stride wide sep room mem
  intro j
  let m := ShrinkMotifOrder.entries X j
  have he : (ShrinkMotifOrder.stateNumber X m).val = j.val :=
    (ShrinkMotifOrder.entries_ordinal X m).symm.trans (congrArg Fin.val ((ShrinkMotifOrder.entries X).symm_apply_apply j))
  have pair := pairs m
  change (mem (dense.val+2*(ShrinkMotifOrder.stateNumber X m).val)).val = _ ∧
    (mem (dense.val+2*(ShrinkMotifOrder.stateNumber X m).val+1)).val = _ at pair
  rw [he] at pair
  exact pair

end State

end CompressorRecords.ShrinkTermInputs

end VPVNP
end Computability
end OAI
