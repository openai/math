import OAI.Hierarchy.ProtocolRAMFrozenWindow
import OAI.Hierarchy.ProtocolRAMFrozenWidthFrame
import OAI.Hierarchy.TaggedShorterSlotWidth

namespace OAI
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM ProtocolRAMPackedRanked ProtocolRAMFrozenWidthFrame
open scoped Fin.CommRing

theorem Size.r_base (s : Size) (r : ℕ) : r+2≤ s.base r := by
  have h:=s.start_base r
  unfold Size.rankStart at h
  omega

theorem Size.low_fits (s : Size) (r W : ℕ) (b : Bank) (h : b.Fits W r) : b.Fits W (s.rank r).spread :=
  ⟨h.1,h.2.1,h.2.2.trans (show r≤r+2+4*s.page by omega)⟩

theorem Size.low_safe (s : Size) (r W : ℕ) (b : Bank) (h : b.Fits W r) : Safe b (s.base r) r :=
  ⟨h.2.2.trans (by have := s.r_base r;omega),Or.inr h.2.2⟩

theorem Size.anchor_safe (s : Size) (r W : ℕ) (room : s.stop r<2^W) (f : Fin 4) :
    Safe (s.anchor r f) (s.base r) r := by
  have fit := s.anchor_fits r W room f
  exact ⟨fit.2.2.trans (s.start_base r),Or.inl (show r<r+2+f.val*s.page by omega)⟩

theorem Size.rank_safe (s : Size) (r : ℕ) :
    Safe (s.rank r).group (s.base r) r ∧ Safe (s.rank r).rank (s.base r) r := by
  have first : r < s.rankStart r := by unfold Size.rankStart;omega
  have seq : (s.rank r).group.base+(s.rank r).group.size≤ s.base r := by
    simp only [Size.rank, Size.base, finish, fresh, Layout.rank, Bank.size]
    generalize s.rankStart r + 2*s.rows + 2^groupBits (3*s.rows) = offset
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  refine ⟨⟨seq, Or.inl (first.trans_le (Nat.le_add_right ..))⟩, ⟨le_rfl, Or.inl ?_⟩⟩
  apply first.trans_le
  simp only [Size.rank, Layout.rank, fresh, Nat.add_assoc]
  exact Nat.le_add_right ..

theorem Size.boardFit (s : Size) (r W : ℕ) (hr : s.stop r<2^W) :
    s.base r+(s.C+2*(s.C*2*s.D))≤2^W := by
  change s.widthBase r≤2^W
  unfold Size.stop Size.widthSrc Size.src at hr
  omega

theorem Size.sinkApart (s : Size) (r W : ℕ) (hr : s.stop r<2^W)
    (f : TaggedShorterScatter.Field s.C s.D) :
    (r:Word W)≠TaggedShorterScatter.layout s.C s.D (s.base r) (s.boardFit r W hr) f := by
  intro eq
  have bound:=s.r_base r
  have wr:=s.base_stop r
  have k:=congrArg Fin.val eq
  change (r:Word W).val=s.base r+(TaggedShorterScatter.fieldIndex s.C s.D f).val at k
  rw [Fin.val_cast_of_lt (by omega)] at k
  omega

theorem Size.widthApart (s : Size) (r : ℕ) (x : TaggedShorterSlotWidth.Slot s.groups s.D) :
    r+1≠TaggedShorterSlotWidth.index (s.widthBase r) x := by
  have h:=(TaggedShorterSlotWidth.index_bounds (s.widthBase r) x).1
  have lower:=s.r_base r
  have before : r + 1 < s.base r := by omega
  exact ne_of_lt ((before.trans_le (Nat.le_add_right (s.base r) s.maskWords)).trans_le h)

end Hierarchy.ProtocolRAMFrozenWindow

end OAI
