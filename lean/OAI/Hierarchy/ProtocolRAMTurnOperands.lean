import OAI.Hierarchy.ProtocolRAMTurnRoleData
import OAI.Hierarchy.TaggedWireOldOperands
import OAI.Hierarchy.ProtocolRAMTurnRead
import OAI.Hierarchy.TaggedShorterCommonScan

namespace OAI
/-! # Actual role-compiler and weighted occurrence banks on the same terminal CPU state -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnOperands
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMTurnItinerary AdaptiveProbe ProbeStage CoreBoard HistoryRoles RoleProgram
open scoped Fin.CommRing Classical

variable {h W k attempts w occ : ℕ} (S : PurchaseSampler)

theorem actual_word (age : Bool) (p : Bool → Public S h W k attempts) (right siteID : Bool) :
    (actual S age p right siteID : Word w)=(printed S age p right siteID:Word w) := by
  cases siteID <;> rfl

def total {n : ℕ} (a : Fin n → ℕ) (i : ℕ) := if h : i < n then a ⟨i,h⟩ else 0

def values (b : Board) (old : Fin b.old → Bool → Public S h W k attempts)
    (new : Fin b.edges → Bool → Public S h W k attempts) (key : Fin occ → Fin b.edges)
    (width : Fin occ → ℕ) : Values where
  oldSource := total fun i=>printed S false (old i) false false
  oldTarget := total fun i=>printed S false (old i) true false
  edge := total fun i=>(key i).val
  tailSite := total fun i=>printed S true (new i) false true
  tailRole := total fun i=>printed S true (new i) false false
  headRole := total fun i=>printed S true (new i) true false
  starts := total fun i=>TaggedShorterCommonScan.earlier key width i.val (key i)

private theorem physical (base n : ℕ) (i : Fin n) (m : Memory w) (room : n ≤ 2^w) :
    (RoleROM.bank base n).read m (i.val:Word w)=m (base+i.val) := by
  rw [Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le room)]
  change m (base + i.val % ProtocolRAMPurchaseSampler.span n) = m (base + i.val)
  rw [Nat.mod_eq_of_lt (i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _))]

/-- Even if padding of a bank extends into the following column, no logical access
reaches it. Only the smaller physical frame below endAt is needed from the next passes. -/
theorem reads (b : Board) (old : Fin b.old → Bool → Public S h W k attempts)
    (new : Fin b.edges → Bool → Public S h W k attempts) (key : Fin occ → Fin b.edges)
    (width : Fin occ → ℕ) (initial out : Memory w) (ready : b.Ready w)
    (seenOld : ∀i side,Resolved S b.chart (b.before side) initial (i.val:Word w) (old i side))
    (seenNew : ∀i side,Resolved S b.chart (b.finish side) initial (i.val:Word w) (new i side))
    (room : siteLast h (2^W) k+1 ≤ 2^w) (low : ∀a < b.endAt,out a=b.final initial a)
    (keyBank : Bank) (dst prefixBits : ℕ) (keyRoom : occ ≤ keyBank.size)
    (rankRoom : 4*occ ≤ 2^prefixBits) (wordRoom : 4*occ ≤ 2^w)
    (keys : ∀i : Fin occ,out (keyBank.base+i.val)=((key i).val:Word w))
    (rank : ∀i : Fin occ,out (dst+4*i.val+3)=(TaggedShorterCommonScan.earlier key width i.val (key i):Word w)) :
    (b.itinerary keyBank ⟨dst+3,prefixBits⟩).Reads (values S b old new key width) b.old occ b.edges out := by
  have bound := ready.room
  unfold Board.endAt Board.newBase at bound
  have oldRoom : b.old ≤ 2^w := by omega
  have newRoom : b.edges ≤ 2^w := by omega
  have left (i : Fin b.old) (side : Bool) :
      (b.oldRole side).read out (i.val:Word w)=(printed S false (old i) side false:Word w) := by
    have obs := (b.old_observed S initial ready i (old i) (seenOld i) room side).2
    have same : (b.oldRole side).read out (i.val:Word w)=(b.oldRole side).read (b.final initial) (i.val:Word w) := by
      unfold Board.oldRole
      rw [physical _ _ i _ oldRoom,physical _ _ i _ oldRoom]
      apply low
      unfold Board.endAt Board.newBase
      have hi := i.isLt
      cases side <;> simp <;> omega
    exact same.trans (obs.trans (actual_word S ..))
  have right (i : Fin b.edges) (side : Bool) :
      (b.newSite side).read out (i.val:Word w)=(printed S true (new i) side true:Word w) ∧
      (b.newRole side).read out (i.val:Word w)=(printed S true (new i) side false:Word w) := by
    have obs := b.new_observed S initial ready i (new i) (seenNew i) room side
    constructor
    · refine Eq.trans ?_ (obs.1.trans (actual_word S ..))
      unfold Board.newSite
      rw [physical _ _ i _ newRoom,physical _ _ i _ newRoom]
      apply low
      unfold Board.endAt
      have hi := i.isLt
      cases side <;> simp <;> omega
    · refine Eq.trans ?_ (obs.2.trans (actual_word S ..))
      unfold Board.newRole
      rw [physical _ _ i _ newRoom,physical _ _ i _ newRoom]
      apply low
      unfold Board.endAt
      have hi := i.isLt
      cases side <;> simp <;> omega
  constructor
  · intro i hi
    simpa [values,total,hi,Board.itinerary] using left ⟨i,hi⟩ false
  · intro i hi
    simpa [values,total,hi,Board.itinerary] using left ⟨i,hi⟩ true
  · intro i hi
    change out (keyBank.base+(i:Word w).val%keyBank.size)=_
    rw [Fin.val_cast_of_lt (by omega),Nat.mod_eq_of_lt (hi.trans_le keyRoom)]
    simpa [values,total,hi] using keys ⟨i,hi⟩
  · intro i hi
    simpa [values,total,hi,Board.itinerary] using (right ⟨i,hi⟩ false).1
  · intro i hi
    simpa [values,total,hi,Board.itinerary] using (right ⟨i,hi⟩ false).2
  · intro i hi
    simpa [values,total,hi,Board.itinerary] using (right ⟨i,hi⟩ true).2
  · intro i hi
    change out (dst+3+((4*i:ℕ):Word w).val%(2^prefixBits))=_
    rw [Fin.val_cast_of_lt (by omega),Nat.mod_eq_of_lt (by omega),
      show dst+3+4*i=dst+4*i+3 by omega]
    simpa [values,total,hi] using rank ⟨i,hi⟩

end Hierarchy.ProtocolRAMTurnOperands

end
end OAI
