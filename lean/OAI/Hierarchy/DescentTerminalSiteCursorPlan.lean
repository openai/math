import OAI.Hierarchy.DescentTerminalRowArena
import OAI.Hierarchy.DescentTerminalRowOwner

namespace OAI
/-! # Site owners from the actual six-column book, mounted markers and paid-row cursors -/
namespace Hierarchy.DescentTerminalRowArena.Arena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalRecipeRows
open DescentTerminalBinPack DescentTerminalSpanBook DescentTerminalHeaderScatter
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable (A : Arena) {w W q G V M K a : ℕ}

theorem mounted_read (m : Memory w) (b : Bank) (safe : b.Fits w A.start) (x : Word w) :
    b.read (A.mount m) x = b.read m x :=
  A.mount_before _ ((Nat.add_lt_add_left (Nat.mod_lt x.val safe.1) _).trans_le safe.2.2)

theorem mounted_half_header (fit : A.finish < 2^w) (m : Memory w) (i : Fin A.sites) :
    A.row.mark.half.read (DescentTerminalRowPlan.header A.row A.sites (A.mount m))
      ((field i 0).val : Word w) = (i.val : Word w) := by
  let j := field i 0
  have inside : j.val < 2*A.sites := j.isLt
  have capacity := A.stride_min
  have small : j.val < A.stride := by omega
  have bank := A.fits_band fit (by decide : 1 < 2) (by decide)
  have low : A.atBand 1 + j.val < A.atBand 2 :=
    (Nat.add_lt_add_left small _).trans_le (A.band_after (by decide : 1 < 2))
  change DescentTerminalRowPlan.header A.row A.sites (A.mount m)
    (A.atBand 1 + (j.val : Word w).val % A.stride) = _
  rw [Fin.val_cast_of_lt (small.trans bank.2.1),Nat.mod_eq_of_lt small,
    A.header_before (A.mount m) low,A.mount_half m inside]
  apply congrArg (fun u : ℕ => (u : Word w))
  change (2*i.val+0)/2=i.val
  omega

/-- The two physical header words for a site are computed by the allocator
from its encoded port book and the common count/boundary dictionaries. -/
theorem mounted_first_last (m : Memory w) (low : A.Lower w) (fit : A.finish < 2^w)
    (sites : Fin A.sites → Site) (f : ∀ i, DescentTerminalLocalPortBook.Room (sites i) G V M K)
    (labels : ∀ i,(sites i).Name → Word a) (refs : ∀ i,(sites i).Arg → Word a)
    (wp : 0<W) (perSite : ∀ i,(sites i).rows q ≤ W)
    (paid : purchased W (counts (q:=q) sites) ≤ A.rows) (counter : A.rows+W < 2^w)
    (boundaryRoom : A.boundaries+(A.rows+1) ≤ A.start)
    (issued : Book.Issued A.parts (fun i => issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM : ∀ j : Fin (Book.Bytes G V M K a),A.countTable.read m (j.val : Word w) = DescentTerminalLocalPortBook.countTable q j)
    (boundaryROM : ∀ j : Fin (A.rows+1),m (A.boundaries+j.val) = (DescentTerminalBinPackCheap.boundaries w W A.rows)[j.val]'j.isLt)
    (i : Fin A.sites) :
    let H := DescentTerminalRowPlan.header A.row A.sites (A.mount m)
    H (A.row.siteFirst.base+i.val) = (first W (counts (q:=q) sites) i : Word w) ∧
      H (A.row.siteLast.base+i.val) = (last W (counts (q:=q) sites) i : Word w) := by
  have width := A.stride_min
  have enough : A.sites ≤ A.stride := by omega
  have books : Book.Issued A.parts (fun i => issue (sites i) (f i) (labels i) (refs i)) (A.mount m) :=
    ⟨fun j k => (A.mounted_read m _ (low.source k) _).trans (issued.source j k),
      fun k v => (A.mounted_read m _ (low.weights k) _).trans (issued.values k v)⟩
  apply DescentTerminalRowPlan.first_last A.row sites f labels refs (A.mount m) (A.row_room low fit)
    wp perSite paid counter ⟨enough,enough,enough⟩ (A.lower_band low.counts 2)
    ((Nat.add_le_add_left enough _).trans (A.band_after (by decide : 3<4)))
    (boundaryRoom.trans (A.start_le 2)) (boundaryRoom.trans (A.start_le 4)) books _ _ i
  · intro j
    exact (A.mounted_read m _ low.counts _).trans (countsROM j)
  · intro j
    exact (A.mount_before _ ((Nat.add_lt_add_left j.isLt _).trans_le boundaryRoom)).trans (boundaryROM j)

/-- The marker, counted cursor and selected local row are the outputs of the
actual row-plan program, including all unoccupied rows of the paid bin array. -/
theorem issued_owner (m : Memory w) (low : A.Lower w) (fit : A.finish < 2^w)
    (sites : Fin A.sites → Site) (f : ∀ i, DescentTerminalLocalPortBook.Room (sites i) G V M K)
    (labels : ∀ i,(sites i).Name → Word a) (refs : ∀ i,(sites i).Arg → Word a)
    (wp : 0<W) (perSite : ∀ i,(sites i).rows q ≤ W)
    (paid : purchased W (counts (q:=q) sites) ≤ A.rows) (counter : A.rows+W < 2^w)
    (boundaryRoom : A.boundaries+(A.rows+1) ≤ A.start)
    (issued : Book.Issued A.parts (fun i => issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM : ∀ j : Fin (Book.Bytes G V M K a),A.countTable.read m (j.val : Word w) = DescentTerminalLocalPortBook.countTable q j)
    (boundaryROM : ∀ j : Fin (A.rows+1),m (A.boundaries+j.val) = (DescentTerminalBinPackCheap.boundaries w W A.rows)[j.val]'j.isLt)
    (i : Fin A.rows) :
    A.row.locate.Facts sites i perSite (DescentTerminalRowPlan.result A.row A.sites A.rows (A.mount m)) := by
  have width := A.stride_min
  have enough : A.sites ≤ A.stride := by omega
  have bank := A.fits_band fit (by decide : 6<7) (by decide)
  have links : DescentTerminalRowPlan.Linked (w:=w) A.row A.sites :=
    ⟨rfl,rfl,rfl,rfl,enough,enough,bank⟩
  have endpoints := A.mounted_first_last m low fit sites f labels refs wp perSite paid counter boundaryRoom issued countsROM boundaryROM
  have room : A.stride < 2^w := bank.2.1
  have pos : 0 < w := by
    by_contra h
    have zero : w = 0 := by omega
    simp only [zero,Nat.pow_zero] at room
    omega
  exact DescentTerminalRowPlan.owner A.row sites (A.mount m) (A.row_room low fit) links perSite pos wp paid
    (enough.trans_lt room) (by omega) (show A.rows ≤ A.stride by omega) (A.mounted_half_header fit m)
    (fun j => (endpoints j).1) (fun j => (endpoints j).2) i

end
end Hierarchy.DescentTerminalRowArena.Arena

end OAI
