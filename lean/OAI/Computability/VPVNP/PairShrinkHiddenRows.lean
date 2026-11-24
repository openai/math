import OAI.Computability.VPVNP.PairShrinkHiddenParser
import OAI.Computability.VPVNP.PairShrinkHiddenGuess
import OAI.Computability.VPVNP.CompressorShrinkResidentLayout

/-!
# The native absorbed-field loop on a shrinking history

The owner's external count and ID row enumerate its hidden fields in the
kernel reader's order. Each ID addresses the actual chosen motif term and
the private interval reserved for that field. The loop consumes the bits
of each hidden word in little-endian order.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkHiddenRows

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif
open CompressorRecords ShrinkHistoryRows ShrinkSliceSweep LocalHistory NetworkKernel
open MotifBlocks MotifGrid MotifConversion
open scoped Classical Fin.CommRing

variable {a l W n A : ℕ} (X : State a (packingLaneBits a l))

/-- Stage inputs read from the physical term allocation and preimage directory. -/
def args (T : Allocation W n A) (p : Fin 6 → Word W) (v : (X.Base × BitWord (Shrink.J a)) × BitWord l)
    (scratchBase slotStride : ℕ) : ShrinkHiddenGuess.Args W where
  termBase := (T.termBase : Word W)
  termStride := (T.termStride : Word W)
  layout := T.layout
  selectorBits := T.selectors
  scratchBase := scratchBase
  slotStride := slotStride
  countBase := (p 3).val
  owner := ((packedOrder X).entries.symm v).val
  rowBase := (p 5).val
  rowStride := (p 4).val

/-- The stored count is the number of complete word fields in this row. -/
theorem count (T : Allocation W n A) (p : Fin 6 → Word W) (m : Memory W)
    (dir : Directory (hiddenOrder X) (packedOrder X) (X.packingData.shrinkInternalOwner T.layout) p m)
    (widths : X.packingData.Motif → Bool × Fin 4 → ℕ) (v : (X.Base × BitWord (Shrink.J a)) × BitWord l)
    (h : Placed (X.packingData.shrinkInternalOwner T.layout) (internalLabel widths T.layout) v)
    (scratchBase slotStride : ℕ) :
    let g := args X T p v scratchBase slotStride
    (m (g.countBase+g.owner)).val = (ShrinkHiddenSlots.rows X T.layout widths v h).length := by
  simpa only [args, ShrinkHiddenSlots.rows, List.length_ofFn] using dir.count v

/-- The resident directory allocation fits both the count probe and the full
exclusive row end, even at the last owner. -/
theorem directory_fit (T : Allocation W n A) (first : ℕ) (v : (X.Base × BitWord (Shrink.J a)) × BitWord l)
    (fit : (ShrinkResidentLayout.layout X first).endAddr < 2^W) (scratchBase slotStride : ℕ)
    (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
    (h : Placed (X.packingData.shrinkInternalOwner T.layout) (internalLabel widths T.layout) v) :
    let p := (ShrinkResidentLayout.layout X first).params a false W
    let g := args X T p v scratchBase slotStride
    g.countBase+g.owner < 2^W ∧ g.row+(ShrinkHiddenSlots.rows X T.layout widths v h).length < 2^W := by
  let L := ShrinkResidentLayout.layout X first
  let idx := ((packedOrder X).entries.symm v).val
  let cap := ShrinkResidentLayout.rowCapacity a false
  have hi : idx < L.sites := ((packedOrder X).entries.symm v).isLt
  have sz : L.size false = L.sites * cap := ShrinkResidentLayout.size_eq_rows X first false
  obtain ⟨_,_,_,_,hc,hs,hr⟩ := ShrinkResidentLayout.frame X first false fit
  have len : (ShrinkHiddenSlots.rows X T.layout widths v h).length = cap := by
    rw [ShrinkHiddenSlots.rows, List.length_ofFn]
    change Fintype.card {e : X.packingData.Motif × Fin 4 // v = X.packingData.shrinkInternalOwner T.layout e} = _
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => eq_comm))).trans (hidden_count X T.layout v)
  change (L.params a false W 3).val+idx < 2^W ∧
    (L.params a false W 5).val+idx*(L.params a false W 4).val+(ShrinkHiddenSlots.rows X T.layout widths v h).length < 2^W
  rw [hc,hs,hr,len]
  have rend := (L.ranges false).2.2.2
  have cend := (L.ranges false).2.2.1
  have bound := Nat.mul_le_mul_right cap hi
  rw [Nat.succ_mul] at bound
  change L.endAddr < 2^W at fit
  change L.counts false+idx < 2^W ∧ L.rows false+idx*cap+cap < 2^W
  omega

section Term

set_option maxHeartbeats 2000000

variable {K : Type*} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (sel : X.ShrinkSelection F)

/-- The physical row uses the supply widths of the chosen motif terms. -/
abbrev widths (motif : X.packingData.Motif) :=
  X.packingData.shrinkSupplyWidths X.shrinkNumber X.packingWidth F motif (sel motif)

/-- The shrinking slice-table allocation specialized to the state's dense motif count and
absolute old-arc count, including the selected term records used for width lookup. -/
abbrev TermAllocation :=
  Allocation W (((Fintype.card X.Base*(2^(Shrink.J a)*2^l))*2^a)*pieceCount (2^a) (Shrink.colors a))
    (Slots.oldBaseArcCount (Fintype.card X.Base) (2^(Shrink.J a)) (2^a) (Shrink.colors a)*2^l)

variable (T : TermAllocation (W := W) X) (p : Fin 6 → Word W) (m : Memory W)

/-- Every stored dense ID and native width agree with the chosen hidden
word, and each word fits its private slot. -/
theorem valid_rows (term : Terms X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex) T F X.packingWidth sel m)
    (allocation : T.Fits) (selectors : T.selectors.val = F.selectorBits)
    (dir : Directory (hiddenOrder X) (packedOrder X) (X.packingData.shrinkInternalOwner T.layout) p m)
    (v : (X.Base × BitWord (Shrink.J a)) × BitWord l)
    (h : Placed (X.packingData.shrinkInternalOwner T.layout) (internalLabel (widths X F sel) T.layout) v)
    (scratchBase slotStride : ℕ)
    (slots : ∀ motif t, widths X F sel motif (!T.layout,t) ≤ slotStride)
    (space : scratchBase+(hiddenOrder X).length*slotStride < 2^W)
    (rowFit : (args X T p v scratchBase slotStride).row + (ShrinkHiddenSlots.rows X T.layout (widths X F sel) v h).length ≤ 2^W) :
    ShrinkHiddenGuess.ValidRows (args X T p v scratchBase slotStride) m (ShrinkHiddenSlots.rows X T.layout (widths X F sel) v h) := by
  let G := args X T p v scratchBase slotStride
  let row := ShrinkHiddenSlots.rows X T.layout (widths X F sel) v h
  let ord := residents (hiddenOrder X) (X.packingData.shrinkInternalOwner T.layout) v
  have hlen : row.length = ord.length := List.length_ofFn
  intro i
  let j : Fin ord.length := ⟨i.val, hlen ▸ i.isLt⟩
  let e := (ord.entries j).val
  let dense := ShrinkMotifOrder.stateNumber X e.1
  let fieldWidth := widths X F sel e.1 (!T.layout,e.2)
  let key := ShrinkHiddenSlots.id X e
  have hkey : key = dense.val*4+e.2.val := ShrinkHiddenSlots.id_eq X e.1 e.2
  have hslot := slots e.1 e.2
  have hkeyBound : key < (hiddenOrder X).length := ((hiddenOrder X).entries.symm e).isLt
  have slotBound : G.slot key + fieldWidth < 2^W := by
    have le := Nat.mul_le_mul_right slotStride hkeyBound
    rw [Nat.succ_mul] at le
    change scratchBase+key*slotStride+fieldWidth < 2^W
    omega
  have hwidth : fieldWidth < 2^W := by omega
  have hfitID : key < 2^W := by
    have room := T.term_stop allocation dense
    have hmul := Nat.mul_le_mul_left dense.val (show 4 ≤ T.termStride by have := allocation.termStride; omega)
    have hbase : T.widthBase ≤ T.widthEnd := Nat.le_add_right ..
    have hend : T.widthEnd ≤ T.last := Nat.le_add_right ..
    have fit := allocation.room
    have ht := e.2.isLt
    rw [hkey]
    unfold Allocation.termStart at room
    omega
  have pos : ((G.row+i.val : ℕ) : Word W).val = G.row+i.val := Fin.val_cast_of_lt ((Nat.add_lt_add_left i.isLt G.row).trans_le rowFit)
  have stored : m (G.row+i.val) = (key : Word W) := ShrinkHiddenSlots.directory_id X T.layout p m dir v j
  have ident : (m (G.row+i.val)).val = key := by rw [stored, Fin.val_cast_of_lt hfitID]
  have width : (G.width m (m (G.row+i.val))).val = fieldWidth := by
    have hdense : (ShrinkMotifOrder.stateNumber X).symm dense = e.1 := Equiv.symm_apply_apply ..
    have got := ShrinkHiddenWidth.term_value_eq X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex)
      T F X.packingWidth sel m term allocation selectors dense e.2 (m (G.row+i.val)) (ident.trans hkey)
      (by change X.packingData.termWidths F X.shrinkNumber X.packingWidth sel
              ((ShrinkMotifOrder.stateNumber X).symm dense) (!T.layout) e.2 < 2^W
          rw [hdense]; exact hwidth)
    change _ = X.packingData.termWidths F X.shrinkNumber X.packingWidth sel
      ((ShrinkMotifOrder.stateNumber X).symm dense) (!T.layout) e.2 at got
    rw [hdense] at got
    exact got
  have rowKey : row[i.val].1 = key := by simp only [row, ShrinkHiddenSlots.rows, List.getElem_ofFn]; rfl
  have rowWidth : row[i.val].2.length = fieldWidth := by
    simp only [row, ShrinkHiddenSlots.rows, List.getElem_ofFn, List.length_ofFn]
    rfl
  change ShrinkHiddenGuess.ValidAt G m (G.row+i.val) row[i.val]
  unfold ShrinkHiddenGuess.ValidAt
  rw [pos, rowKey, rowWidth]
  exact ⟨ident, width, slotBound⟩

end Term

section Kernel

variable {K R : Type*} [_root_.Field K] [CommRing R] {S : BlockSchedule K}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)

/-- The native loop consumes the scheduled kernel's exact encoding of
the hidden assignment. -/
theorem kernel_stream {l : ℕ} (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) l))
    (s : X.ShrinkSelection B.shrink) (v old new)
    (x : (B.shrinkPassWitnesses f hf i rfl X s v old new).Choice) :
    let layout := X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s
    let widths := fun m => X.packingData.shrinkSupplyWidths X.shrinkNumber X.packingWidth B.shrink m (s m)
    ShrinkHiddenGuess.stream (ShrinkHiddenSlots.rows X layout widths v x.1) =
      ((shrinkPassReaders B f hf i rfl X).kernel s v old new).encode x := by
  intro layout widths
  rw [ShrinkHiddenGuess.stream, List.flatMap_def]
  exact (ShrinkHiddenSlots.kernel_encode B f hf i X s v old new x).symm

end Kernel
end PairSimulation.ShrinkHiddenRows

end

end VPVNP
end Computability
end OAI
