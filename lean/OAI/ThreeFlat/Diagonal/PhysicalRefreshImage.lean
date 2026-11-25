import OAI.ThreeFlat.Diagonal.PhysicalRefreshFamily
import OAI.ThreeFlat.Diagonal.SlotBaseChart
import OAI.ThreeFlat.Diagonal.SlotImageViews
import OAI.ThreeFlat.Diagonal.CompressorShiftSlices

namespace OAI
/-! # The physical refresh record and RAM share their old graph and demand order -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking Native RefreshTies RefreshDemandRows
open scoped Classical BigOperators
noncomputable section

variable {s rem : ℕ} (A : State (2^s) (s+rem))

abbrev numberedRefreshGraph := SlotImage.inBaseChart (refreshBinaryGraph A) A.order

def numberedRefreshWidths : SlotImage.RefreshInput (Fintype.card A.Base) s rem → ℕ :=
  (fun p=>A.width (p.1,(splitWord s rem).symm p.2)) ∘ (SlotImage.baseEdges A.order).symm

theorem refreshImage (C : SlotImage.Columns) (mem : ℕ → ℕ)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal (s+rem)) C mem A.width) :
    SlotImage.Stored (numberedRefreshGraph A) (Equiv.refl _) (SlotImage.pairLane (tagOrdinal s) (tagOrdinal rem))
      C mem (numberedRefreshWidths A) := by
  apply SlotImage.inBaseChart_stored
  rw [Equiv.trans_refl]
  refine ⟨old.rowCount,?_,?_⟩
  · intro p back i
    rw [old.graph]
    fin_cases i
    · rfl
    · rfl
    · change (tagOrdinal (s+rem) (SlotImage.shift A.graph back p)).val =
        (SlotImage.pairLane (tagOrdinal s) (tagOrdinal rem) (SlotImage.shift (refreshBinaryGraph A) back p)).val
      rw [ordinal_split,SlotImage.pairLane_val]
      cases back <;> rfl
  · intro e
    have h := old.widthWord (e.1,(splitWord s rem).symm e.2)
    simpa only [SlotImage.edgeOrdinal,SlotImage.pairLane_val,Nat.pow_add,ordinal_split,
      AddEquiv.apply_symm_apply,Nat.add_assoc] using h

def numBlock (z : A.Base × BitWord rem) : Block (Fintype.card A.Base) rem := (A.order z.1,z.2)

def numAddress (e : Address (A.Base × BitWord rem) (2^s)) : Address' (Fintype.card A.Base) s rem :=
  (numBlock A e.1,e.2)

theorem numArrival (z : A.Base × BitWord rem) (dir : Bool) (i j : Fin (2^s)) :
    addr (arrival (numberedRefreshGraph A) (tagOrdinal s).symm) (numBlock A z) (dir,i,j) =
      numAddress A (addr (arrival (refreshBinaryGraph A) (tagOrdinal s).symm) z (dir,i,j)) := by
  cases dir with
  | false => rfl
  | true =>
    obtain ⟨v,l⟩ := z
    have cancel (p : A.Base × Fin (2^s)) : Prod.map A.order.symm id (Prod.map A.order id p)=p := by
      cases p
      simp
    change (((_,_),_,_):Address' (Fintype.card A.Base) s rem)=_
    simp [numAddress,numBlock,addr,arrival,slotAddress,numberedRefreshGraph,SlotImage.inBaseChart,
      SlotImage.baseSlots,LiftedSlots.actualTarget,cancel]

theorem numWidth (e : Address (A.Base × BitWord rem) (2^s)) :
    SlotImage.demandWidth (numberedRefreshWidths A) (numAddress A e)=refreshBinaryInput A e := by
  obtain ⟨⟨v,l⟩,i,j⟩ := e
  simp [SlotImage.demandWidth,numberedRefreshWidths,numAddress,numBlock,refreshBinaryInput,
    refreshInput,StageAddress.refreshEdge,slotAddress,SlotImage.baseEdges,SlotImage.baseSlots]

theorem numProfile (z : A.Base × BitWord rem) :
    profile (numberedRefreshGraph A) (tagOrdinal s).symm (SlotImage.demandWidth (numberedRefreshWidths A))
      (numBlock A z)=profile (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) z := by
  funext e
  obtain ⟨dir,i,j⟩ := e
  exact (congrArg (SlotImage.demandWidth (numberedRefreshWidths A)) (numArrival A z dir i j)).trans (numWidth A _)

theorem blockOrder_numeric (z : A.Base × BitWord rem) :
    (refreshBlockOrder A z).val=blockId (numBlock A z) := refreshBlockOrder_val A z

end

end ThreeFlat.Diagonal.PhysicalStage

end OAI
