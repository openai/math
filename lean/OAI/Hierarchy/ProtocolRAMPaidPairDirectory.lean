import OAI.Hierarchy.ProtocolRAMPaidWidthCore
import OAI.Hierarchy.ProtocolRAMCalendarVerdict
import OAI.Hierarchy.ProtocolRAMOccurrenceHeader

namespace OAI
/-! # Public ordinal and parity words shared by every paid-width scatter -/

namespace Hierarchy.ProtocolRAM.PaidPairDirectory

open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open RepairHistogram
open scoped Fin.CommRing
variable {W q d : ℕ}

/-- Largest real slice in the chronological scatter list. -/
def maxCount (ss : List PaidWidths.Slice) := ss.foldr (fun s n=>max s.count n) 0

theorem count_le {ss : List PaidWidths.Slice} {s : PaidWidths.Slice} (h : s∈ss) :
    s.count≤ maxCount ss := by
  induction ss with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl|tail
    · exact le_max_left _ _
    · exact (ih tail).trans (le_max_right _ _)

/-- A pair of adjacent public advice banks with the same power-of-two capacity. -/
def banks (base bits : ℕ) : Bank × Bank := (⟨base,bits⟩,⟨base+2^bits,bits⟩)

theorem banks_room (base bits cap : ℕ) (fits : 2*cap≤2^bits) :
    2*cap≤(banks base bits).1.size ∧ 2*cap≤(banks base bits).2.size ∧
    (banks base bits).1.base+2*cap≤(banks base bits).2.base :=
  ⟨fits,fits,Nat.add_le_add_left fits base⟩

def occupied (occ parity : Bank) (cap x : ℕ) :=
  (occ.base≤x ∧ x<occ.base+2*cap) ∨ (parity.base≤x ∧ x<parity.base+2*cap)

/-- These are the two numerical tables used by the existing repair code. -/
def mount (occ parity : Bank) (cap : ℕ) (m : Memory W) : Memory W :=
  pairAdvice ⟨occ,parity,.lit 0,.lit 0,.lit 0⟩ cap m

def Reads (occ parity : Bank) (cap : ℕ) (m : Memory W) : Prop :=
  ∀ i : Fin (2*cap),m (occ.base+i.val)=((i.val/2:ℕ):Word W) ∧
    m (parity.base+i.val)=((i.val%2:ℕ):Word W)

theorem read_mount (occ parity : Bank) (cap : ℕ) (m : Memory W)
    (disjoint : occ.base+2*cap≤parity.base) : Reads occ parity cap (mount occ parity cap m) := by
  intro i
  have small:=i.isLt
  constructor
  · simp [mount,pairAdvice,fillSegment,
      show ¬(parity.base≤occ.base+i.val ∧ occ.base+i.val<parity.base+2*cap) by omega,
      show occ.base≤occ.base+i.val ∧ occ.base+i.val<occ.base+2*cap by omega]
  · simp [mount,pairAdvice,fillSegment,
      show parity.base≤parity.base+i.val ∧ parity.base+i.val<parity.base+2*cap by omega]

theorem frame (occ parity : Bank) (cap : ℕ) (m : Memory W) (x : ℕ)
    (outside : ¬occupied occ parity cap x) : mount occ parity cap m x=m x := by
  have a : ¬(occ.base≤x ∧ x<occ.base+2*cap) := fun h=>outside (.inl h)
  have b : ¬(parity.base≤x ∧ x<parity.base+2*cap) := fun h=>outside (.inr h)
  simp [mount,pairAdvice,fillSegment,a,b]

theorem Reads.transfer {occ parity : Bank} {cap : ℕ} {m after : Memory W} (read : Reads occ parity cap m)
    (kept : ∀ x,occupied occ parity cap x→after x=m x) : Reads occ parity cap after := by
  intro i
  have small:=i.isLt
  exact ⟨(kept _ (.inl ⟨by omega,by omega⟩)).trans (read i).1,
    (kept _ (.inr ⟨by omega,by omega⟩)).trans (read i).2⟩

/-- Run all actual calendar events and its final acceptance write. -/
theorem checked_reads (C : Calendar.Chart W q d) (flag : ℕ) (m : Memory W) {occ parity : Bank} {cap : ℕ}
    (read : Reads occ parity cap m) (ready : Calendar.mounted C (Calendar.events C.mesh) m)
    (free : ∀ x,occupied occ parity cap x→∀ ev∈Calendar.events C.mesh,Calendar.protected C x ev)
    (off : ¬occupied occ parity cap flag) : Reads occ parity cap (Calendar.checkedOut C flag m) := by
  apply read.transfer
  intro x hx
  have ne : x≠flag := fun h=>off (h ▸ hx)
  unfold Calendar.checkedOut
  rw [ProtocolRAMGeneratedWrite.frame_image flag 1 _ _ x (by omega)]
  exact Calendar.run_frame C _ _ x ready (free x hx)

/-- A slice reads exactly the first `2*count` words of the public table. -/
theorem directory {occ parity : Bank} {cap : ℕ} {m : Memory W} (read : Reads occ parity cap m)
    (size : 2*cap≤2^W) (ownerRoom : 2*cap≤occ.size) (tagRoom : 2*cap≤parity.size)
    (wide : 0<W) (s : PaidWidths.Slice) (bank : Bank) (edges : ℕ)
    (own : s.owner=occ) (tag : s.parity=parity) (count : s.count≤cap) :
    PairDirectory (s.columns bank edges) m s.count := by
  have evenRead (k : ℕ) (hk : k<2*cap) : parity.read m (k:Word W)=((k%2:ℕ):Word W) := by
    simpa only [Bank.read,Fin.val_cast_of_lt (hk.trans_le size),Nat.mod_eq_of_lt (hk.trans_le tagRoom)]
      using (read ⟨k,hk⟩).2
  have posRead (k : ℕ) (hk : k<2*cap) : occ.read m (k:Word W)=((k/2:ℕ):Word W) := by
    simpa only [Bank.read,Fin.val_cast_of_lt (hk.trans_le size),Nat.mod_eq_of_lt (hk.trans_le ownerRoom)]
      using (read ⟨k,hk⟩).1
  constructor
  · intro j
    change s.parity.read m _=0
    rw [tag,evenRead _ (by have:=j.isLt;omega),show (2*j.val)%2=0 by omega,Nat.cast_zero]
  · intro j
    change s.parity.read m _≠0
    rw [tag,evenRead _ (by have:=j.isLt;omega),show (2*j.val+1)%2=1 by omega]
    intro zero
    have bad:=congrArg Fin.val zero
    rw [Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne')] at bad
    exact Nat.one_ne_zero bad
  · intro j
    change s.owner.read m _=_
    rw [own,posRead _ (by have:=j.isLt;omega),show 2*j.val/2=j.val by omega]
  · intro j
    change s.owner.read m _=_
    rw [own,posRead _ (by have:=j.isLt;omega),show (2*j.val+1)/2=j.val by omega]

/-- Direct, mate and broadcast rows reuse the corresponding occurrence
header already loaded by the economic controller. -/
theorem of_header (h : Calendar.StockCommit.PortHeader) {m : Memory W} (loaded : h.Loaded m)
    (s : PaidWidths.Slice) (bank : Bank) (edges : ℕ) (own : s.owner=h.owner)
    (tag : s.parity=h.parity) (short : s.count≤h.count) :
    PairDirectory (s.columns bank edges) m s.count := by
  have actual:=loaded.pair.restrict short
  constructor
  · intro i; change s.parity.read m _=0; rw [tag]; exact actual.first i
  · intro i; change s.parity.read m _≠0; rw [tag]; exact actual.second i
  · intro i; change s.owner.read m _=_; rw [own]; exact actual.firstRow i
  · intro i; change s.owner.read m _=_; rw [own]; exact actual.secondRow i

theorem mounted_checked (C : Calendar.Chart W q d) (flag : ℕ) (m : Memory W) {occ parity : Bank} {cap : ℕ}
    (read : Reads occ parity cap m) (ready : Calendar.mounted C (Calendar.events C.mesh) m)
    (free : ∀ x,occupied occ parity cap x→∀ ev∈Calendar.events C.mesh,Calendar.protected C x ev)
    (off : ¬occupied occ parity cap flag) (size : 2*cap≤2^W)
    (ownerRoom : 2*cap≤occ.size) (tagRoom : 2*cap≤parity.size) (wide : 0<W)
    (bank : Bank) (edges src : ℕ) (ss : List PaidWidths.Slice)
    (layout : ∀ s∈ss,s.Fits bank edges src W ∧ s.owner=occ ∧ s.parity=parity ∧ s.count≤cap) :
    PaidWidths.Mounted bank edges src ss (Calendar.checkedOut C flag m) := by
  have finalRead:=checked_reads C flag m read ready free off
  intro s hs
  obtain ⟨fit,own,tag,count⟩:=layout s hs
  exact ⟨fit,directory finalRead size ownerRoom tagRoom wide s bank edges own tag count⟩

/-- The chronological list can mix loaded direct, mate and broadcast
headers with the shared directory for spill and boundary rows. -/
theorem mixed_mounted {m : Memory W} {occ parity : Bank} {cap : ℕ} (read : Reads occ parity cap m)
    (size : 2*cap≤2^W) (ownerRoom : 2*cap≤occ.size) (tagRoom : 2*cap≤parity.size) (wide : 0<W)
    (bank : Bank) (edges src : ℕ) (ss : List PaidWidths.Slice)
    (fits : ∀ s∈ss,s.Fits bank edges src W)
    (layout : ∀ s∈ss,(∃ h : Calendar.StockCommit.PortHeader,h.Loaded m ∧ s.owner=h.owner ∧
      s.parity=h.parity ∧ s.count≤h.count) ∨ (s.owner=occ ∧ s.parity=parity ∧ s.count≤cap)) :
    PaidWidths.Mounted bank edges src ss m := by
  intro s hs
  refine ⟨fits s hs,?_⟩
  rcases layout s hs with ⟨h,loaded,own,tag,short⟩|⟨own,tag,short⟩
  · exact of_header h loaded s bank edges own tag short
  · exact directory read size ownerRoom tagRoom wide s bank edges own tag short

end Hierarchy.ProtocolRAM.PaidPairDirectory

end OAI
