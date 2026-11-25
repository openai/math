import OAI.Hierarchy.ProtocolRAMTurnOperands
import OAI.Hierarchy.ProtocolRAMTurnChart

namespace OAI
/-! # Joining the directed old-site and width words to the ten positional role/endpoint words -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnRawWords
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles RoleProgram ProtocolRAM ProtocolRAMTurnChart
open scoped Fin.CommRing Classical

variable {h W k attempts w N : ℕ} (S : PurchaseSampler)
def data (b : Board) (site half : Bank) : Data :=
  ⟨b.forwardSite false,b.forwardSite true,b.widthBank,site,b.oldRole false,b.oldRole true,half⟩

def words (b : Board) (p : Fin b.old → Bool → Public S h W k attempts) (width : Fin b.old → ℕ) : Words :=
  ⟨ProtocolRAMTurnOperands.total fun i=>(name (HistoryRoles.site S (p i false))).val,
   ProtocolRAMTurnOperands.total fun i=>(name (HistoryRoles.site S (p i true))).val,
   ProtocolRAMTurnOperands.total width,
   ProtocolRAMTurnOperands.total fun i=>ProtocolRAMTurnOperands.printed S false (p i) false false,
   ProtocolRAMTurnOperands.total fun i=>ProtocolRAMTurnOperands.printed S false (p i) true false⟩

theorem before (b : Board) (g : Inventory) (p : Fin b.old → Bool → Public S h W k attempts)
    (width : Fin b.old → ℕ) (initial m : Memory w) (ready : b.Ready w)
    (fit : ∀j,(b.rawFields g j).Fits w b.base) (room : b.endAt+3*b.old < 2^w)
    (frame : ∀a < b.endAt+3*b.old,m a=b.extendedState g initial a)
    (seen : ∀i side,Resolved S b.chart (b.before side) initial (i.val:Word w) (p i side))
    (widths : ∀i,g.width.eval initial (i.val:Word w)=(width i:Word w))
    (siteRoom : siteLast h (2^W) k+1 ≤ 2^w) (site half : Bank)
    (decode : ∀i side,half.read m (ProtocolRAMTurnOperands.printed S false (p i) side false:Word w)=
      ((ProtocolRAMTurnOperands.printed S false (p i) side false/2:ℕ):Word w))
    (u : Fin N → Geometry) (valid : ∀i,(u i).item < b.old) :
    (data b site half).Before (words S b p width) m u := by
  obtain ⟨_,cells,earlier⟩ := b.extended_exec g initial ready fit room
  have cap (i : Fin b.old) : i.val < 2^w := by have := i.isLt;omega
  have atWord (base : ℕ) (i : Fin b.old) (state : Memory w) :
      (RoleROM.bank base b.old).read state (i.val:Word w)=state (base+i.val) := by
    rw [Bank.read,Fin.val_cast_of_lt (cap i)]
    change state (base + i.val % ProtocolRAMPurchaseSampler.span b.old) = state (base + i.val)
    rw [Nat.mod_eq_of_lt (i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _))]
  have lin (i : Fin b.old) (j : Fin 3) :
      (RoleROM.bank (b.endAt+j.val*b.old) b.old).read m (i.val:Word w)=(b.rawFields g j).eval initial (i.val:Word w) := by
    rw [atWord]
    exact (frame _ (by have := i.isLt;fin_cases j <;> simp <;> omega)).trans (cells j i)
  have low (i : Fin b.old) (side : Bool) :
      (b.oldRole side).read m (i.val:Word w)=(ProtocolRAMTurnOperands.printed S false (p i) side false:Word w) := by
    have control := (b.old_observed S initial ready i (p i) (seen i) siteRoom side).2
    refine Eq.trans ?_ (control.trans (ProtocolRAMTurnOperands.actual_word S ..))
    unfold Board.oldRole
    rw [atWord,atWord]
    have lt : b.base+(2+side.toNat)*b.old+i.val < b.endAt := by
      unfold Board.endAt Board.newBase
      have := i.isLt
      cases side <;> simp <;> omega
    exact (frame _ (by omega)).trans (earlier _ lt)
  have raw (i : Fin b.old) (side : Bool) : (b.forwardSite side).read m (i.val:Word w)=
      ((name (HistoryRoles.site S (p i side))).val:Word w) := by
    cases side
    · exact (lin i 0).trans (seen i false).1
    · exact (lin i 1).trans (seen i true).1
  have wval (i : Fin b.old) : b.widthBank.read m (i.val:Word w)=(width i:Word w) :=
    (lin i 2).trans (widths i)
  let row (i : Fin N) : Fin b.old := ⟨(u i).item,valid i⟩
  constructor
  · exact fun i=>by simpa [data,words,ProtocolRAMTurnOperands.total,valid i,row] using raw (row i) false
  · exact fun i=>by simpa [data,words,ProtocolRAMTurnOperands.total,valid i,row] using raw (row i) true
  · exact fun i=>by simpa [data,words,ProtocolRAMTurnOperands.total,valid i,row] using wval (row i)
  · exact fun i=>by simpa [data,words,ProtocolRAMTurnOperands.total,valid i,row] using low (row i) false
  · exact fun i=>by simpa [data,words,ProtocolRAMTurnOperands.total,valid i,row] using low (row i) true
  · exact fun i=>by simpa [data,words,ProtocolRAMTurnOperands.total,valid i,row] using decode (row i) false
  · exact fun i=>by simpa [data,words,ProtocolRAMTurnOperands.total,valid i,row] using decode (row i) true
  · exact fun i=>by simpa [data,words,ProtocolRAMTurnOperands.total,valid i,row] using
      ((name (HistoryRoles.site S (p (row i) false))).isLt.trans_le siteRoom)
  · exact fun i=>by simpa [data,words,ProtocolRAMTurnOperands.total,valid i,row] using
      ((name (HistoryRoles.site S (p (row i) true))).isLt.trans_le siteRoom)

end Hierarchy.ProtocolRAMTurnRawWords

end
end OAI
