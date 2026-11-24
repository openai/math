import OAI.Computability.VPVNP.PairShrinkHiddenFootprint
import OAI.Computability.VPVNP.PairShrinkHiddenRows
import OAI.Computability.VPVNP.PairTerminalFootprint

/-!
# The selected hidden pass reads below the terminal controller

The count and ID addresses lie in the resident directory. The dense ID
selects a ten-word term row entirely below the width-array head. These two
upper bounds cover every external read, independently of the private bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkHiddenRows

open BurstRAM PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open CompressorRecords ShrinkHistoryRows ShrinkSliceSweep NetworkKernel
open MotifBlocks MotifGrid MotifConversion ShrinkHiddenGuess SourceTransport LocalHistory
open scoped Classical Fin.CommRing

variable {a l W n A : ℕ} (X : State a (packingLaneBits a l))

private theorem row_term_cells (T : Allocation W n A) (fit : T.Fits) (bound : ℕ)
    (termBound : T.widthBase ≤ bound) (id : Word W) (ordinal : Fin n) (role : Fin 4)
    (key : id.val = ordinal.val*4+role.val) :
    let base := ShrinkHiddenWidth.rowBase (T.termBase : Word W) (T.termStride : Word W) id
    let coord := ShrinkHiddenWidth.coordinate (T.layout.toNat : Word W) id
    (base+1).val < bound ∧ (base+2+coord).val < bound := by
  intro base coord
  have room := T.term_stop fit ordinal
  have widthLe : T.widthBase ≤ T.widthEnd := Nat.le_add_right ..
  have endLe : T.widthEnd ≤ T.last := Nat.le_add_right ..
  have fits := fit.room
  unfold Allocation.termStart at room
  have h4 : 4 < 2^W := by omega
  have hi : (!T.layout).toNat*4+role.val < 8 := by have := Bool.toNat_le (!T.layout); have := role.isLt; omega
  dsimp only [base,coord]
  rw [ShrinkHiddenWidth.rowBase_eq _ _ _ _ _ key h4,ShrinkHiddenWidth.coordinate_eq _ _ _ _ key h4]
  let rb : ℕ := T.termBase+ordinal.val*T.termStride
  change (((rb : Word W)+((1 : ℕ) : Word W)).val < bound) ∧
    (((rb : Word W)+((2 : ℕ) : Word W)+(((!T.layout).toNat*4+role.val : ℕ) : Word W)).val < bound)
  rw [← Nat.cast_add,← Nat.cast_add,← Nat.cast_add]
  exact ⟨(Nat.mod_le ..).trans_lt (by dsimp [rb]; omega),(Nat.mod_le ..).trans_lt (by dsimp [rb]; omega)⟩

/-- Actual trace support on the count, row, and term allocations. -/
theorem reads_below (T : TermAllocation (W := W) X) (m : Memory W) (first cutoff : ℕ)
    (allocation : T.Fits) (residentFit : (ShrinkResidentLayout.layout X first).endAddr < 2^W)
    (residentBound : (ShrinkResidentLayout.layout X first).endAddr ≤ cutoff) (termBound : T.widthBase ≤ cutoff)
    (dir : Directory (hiddenOrder X) (packedOrder X) (X.packingData.shrinkInternalOwner T.layout)
      ((ShrinkResidentLayout.layout X first).params a false W) m)
    (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
    (v : (X.Base × BitWord (Shrink.J a)) × BitWord l)
    (h : Placed (X.packingData.shrinkInternalOwner T.layout) (internalLabel widths T.layout) v)
    (scratchBase slotStride : ℕ) :
    let L := ShrinkResidentLayout.layout X first
    let G := args X T (L.params a false W) v scratchBase slotStride
    let es := ShrinkHiddenSlots.rows X T.layout widths v h
    Reads (fun i => i < cutoff) (events G m es) := by
  intro L G es
  let ord := residents (hiddenOrder X) (X.packingData.shrinkInternalOwner T.layout) v
  let own := ((packedOrder X).entries.symm v).val
  let cap := ShrinkResidentLayout.rowCapacity a false
  have ownLt : own < L.sites := ((packedOrder X).entries.symm v).isLt
  obtain ⟨_,_,_,_,hc,hcap,hr⟩ := ShrinkResidentLayout.frame X first false residentFit
  change (L.params a false W 3).val = L.counts false at hc
  change (L.params a false W 4).val = cap at hcap
  change (L.params a false W 5).val = L.rows false at hr
  change L.endAddr ≤ cutoff at residentBound
  change L.endAddr < 2^W at residentFit
  obtain ⟨_,_,countEnd,rowsEnd⟩ := L.ranges false
  have size : L.size false = L.sites*cap := ShrinkResidentLayout.size_eq_rows X first false
  have countCell : G.countBase+G.owner < cutoff := by
    change (L.params a false W 3).val+own < cutoff
    rw [hc]
    calc
      _ < L.counts false+L.sites := Nat.add_lt_add_left ownLt _
      _ = L.rows false := countEnd
      _ ≤ L.rows false+L.size false := Nat.le_add_right ..
      _ ≤ _ := rowsEnd.trans residentBound
  have len : es.length = ord.length := List.length_ofFn
  have lengthCap : ord.length = cap :=
    (Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => eq_comm))).trans (hidden_count X T.layout v)
  have rowCell (i : Fin es.length) : G.row+i.val < L.endAddr := by
    have offset := Nat.mul_le_mul_right cap ownLt
    rw [Nat.succ_mul] at offset
    have il : i.val < cap := i.isLt.trans_eq (len.trans lengthCap)
    change (L.params a false W 5).val+own*(L.params a false W 4).val+i.val < L.endAddr
    rw [hr,hcap,Nat.add_assoc]
    calc
      _ < L.rows false+(own*cap+cap) := Nat.add_lt_add_left (Nat.add_lt_add_left il _) _
      _ ≤ L.rows false+L.sites*cap := Nat.add_le_add_left offset _
      _ ≤ _ := size ▸ rowsEnd
  apply events_reads
  · exact (Nat.mod_le ..).trans_lt countCell
  · intro i
    let j : Fin ord.length := ⟨i.val,len ▸ i.isLt⟩
    let e := (ord.entries j).val
    let dense := ShrinkMotifOrder.stateNumber X e.1
    let ptr := G.row+i.val
    have ptrEq : (ptr : Word W).val = ptr := Fin.val_cast_of_lt ((rowCell i).trans residentFit)
    have stored : m ptr = (ShrinkHiddenSlots.id X e : Word W) :=
      ShrinkHiddenSlots.directory_id X T.layout (L.params a false W) m dir v j
    have hkey := ShrinkHiddenSlots.id_eq X e.1 e.2
    have idLe : (m ptr).val ≤ dense.val*4+e.2.val := by
      rw [stored, Fin.val_natCast, hkey]; exact Nat.mod_le ..
    let ix := (m ptr).val / 4
    let role : Fin 4 := ⟨(m ptr).val % 4,Nat.mod_lt _ (by decide)⟩
    have le : ix ≤ dense.val := by dsimp only [ix]; have := e.2.isLt; omega
    let index := (⟨ix,le.trans_lt dense.isLt⟩ : Fin _)
    have key : (m ptr).val = index.val*4+role.val := by dsimp [index,ix,role]; omega
    have pair := row_term_cells T allocation cutoff termBound (m ptr) index role key
    change (ptr : Word W).val < cutoff ∧ _
    rw [ptrEq]
    exact ⟨(rowCell i).trans_le residentBound,pair⟩

/-- The header and resident scan have a common footprint below the terminal
control region. The two protected control cells are excluded from the
entire chronological trace. -/
theorem hosted_reads {p r : ℕ} (T : TermAllocation (W := W) X) (m : Memory W) (first oldLevel : ℕ)
    (H : Word W) (terminalFit : H.val+31 < 2^W) (levelBound : oldLevel+38 < H.val)
    (allocation : T.Fits) (residentBound : (ShrinkResidentLayout.layout X first).endAddr ≤ H.val)
    (termBound : T.widthBase ≤ H.val)
    (dir : Directory (hiddenOrder X) (packedOrder X) (X.packingData.shrinkInternalOwner T.layout)
      ((ShrinkResidentLayout.layout X first).params a false W) m)
    (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
    (v : (X.Base × BitWord (Shrink.J a)) × BitWord l)
    (h : Placed (X.packingData.shrinkInternalOwner T.layout) (internalLabel widths T.layout) v)
    (scratchBase slotStride s t : ℕ) (inputs : Fin 6 → Fin r)
    (vm : Fin (RegisterSetup.regCount (Header.recipe s t)) ↪ Fin r) (c : Config W p r)
    (level : c.reg (inputs 5) = (oldLevel : Word W)) :
    let L := ShrinkResidentLayout.layout X first
    let G := args X T (L.params a false W) v scratchBase slotStride
    let es := ShrinkHiddenSlots.rows X T.layout widths v h
    let ev := Header.trace s t inputs vm c m ++ events G m es
    Reads (fun i => i < H.val) ev ∧ Reads (TerminalLink.workerCell H) ev := by
  intro L G es ev
  have head := Header.trace_reads (fun i => i < H.val) s t inputs vm c m oldLevel level
    (levelBound.trans H.isLt) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      omega)
  have body := reads_below X T m first H.val allocation (residentBound.trans_lt H.isLt)
    residentBound termBound dir widths v h scratchBase slotStride
  have below : Reads (fun i => i < H.val) ev := by
    intro addr value read
    exact (List.mem_append.mp read).elim (head addr value) (body addr value)
  exact ⟨below,fun addr value read => TerminalFootprint.below H terminalFit (below addr value read)⟩

end PairSimulation.ShrinkHiddenRows

end

end VPVNP
end Computability
end OAI
