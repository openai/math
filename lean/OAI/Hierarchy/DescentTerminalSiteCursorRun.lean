import OAI.Hierarchy.DescentTerminalSiteCursorPlan
import OAI.Hierarchy.DescentTerminalRowArenaSort

namespace OAI
/-! # Site ownership after writing the offset, sort and relative-slot arrays -/
namespace Hierarchy.DescentTerminalRowArena.Arena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalRecipeRows
open DescentTerminalBinPack DescentTerminalSpanBook
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable (A : Arena) {w W q G V M K a : ℕ}

/-- The offset writer, stable packet sort, and relative-slot publisher, applied to the mounted row plan. -/
def siteSockets (positive : 0 < A.sites) (m : Memory w) : Memory w :=
  DescentTerminalPacketSlotRAM.after A.order A.packets A.sites
    (DescentTerminalExteriorPackets.sorted A.homes A.order A.sites A.packets positive
      (DescentTerminalSiteOffsets.result A.offset A.sites (DescentTerminalRowPlan.result A.row A.sites A.rows (A.mount m))))

private theorem sockets_cursor_read (positive : 0 < A.sites) (m : Memory w) (low : A.Lower w) (fit : A.finish < 2^w)
    (j : ℕ) (hj : j < 13) (x : Word w) :
    (A.bank j).read (A.siteSockets positive m) x =
      (A.bank j).read (DescentTerminalRowPlan.result A.row A.sites A.rows (A.mount m)) x := by
  let addr := A.atBand j + x.val % A.stride
  have cap := A.stride_min
  have nz : 0 < A.stride := by omega
  have before : addr < A.atBand 13 :=
    (Nat.add_lt_add_left (Nat.mod_lt x.val nz) _).trans_le (A.band_after hj)
  have src : addr < A.order.src := before.trans_le (A.band_mono (by decide : 13 ≤ 14))
  have sorted : addr < A.order.sorted := before.trans_le (A.band_mono (by decide : 13 ≤ 17))
  have slots : addr < DescentTerminalPacketSlotRAM.out A.order A.packets A.sites :=
    (sorted.trans_le (Nat.le_add_right ..)).trans_le (Nat.le_add_right ..)
  let plan := DescentTerminalRowPlan.result A.row A.sites A.rows (A.mount m)
  let pos := DescentTerminalSiteOffsets.result A.offset A.sites plan
  change DescentTerminalPacketSlotRAM.after A.order A.packets A.sites
    (DescentTerminalExteriorPackets.sorted A.homes A.order A.sites A.packets positive pos) addr = plan addr
  rw [DescentTerminalPacketSlotRAM.retained _ _ _ _ _ (.inl slots),
    DescentTerminalExteriorPackets.sort_before _ _ _ _ pos positive (A.sort_room low fit) src]
  exact DescentTerminalSiteOffsets.early _ _ _ before

/-- The published pool reserves at least one whole bin because even the
first reached site has an output row. The row arena therefore supplies the
allocator's carry word without any additional machine-width premise. -/
theorem purchased_word_room (positive : 0 < A.sites) (fit : A.finish < 2^w) (sites : Fin A.sites → Site)
    (wp : 0<W) (paid : purchased W (counts (q:=q) sites) ≤ A.rows) :
    A.rows+W < 2^w := by
  let c := counts (q:=q) sites
  let i : Fin A.sites := ⟨0,positive⟩
  have nonempty : 0 < c i := by simp [c,Site.rows]
  have occupied := (cursor_mono W c (show i.val+1 ≤ A.sites from i.isLt)).trans (end_le_purchased wp c)
  rw [cursor_step] at occupied
  have binPos : 0 < bins W c := by
    by_contra h
    have zero : bins W c = 0 := by omega
    simp only [purchased,zero,Nat.zero_mul] at occupied
    omega
  have capacity : W ≤ A.rows := (Nat.le_mul_of_pos_left W binPos).trans paid
  have stride : 2*A.sites+A.rows+A.packets+1 < A.stride := A.stride_min
  have room : A.start+22*A.stride < 2^w := fit
  omega

/-- The site-owned spans at the suffix's sockets come from its genuine
allocator, before all packet ranks and relative slots are physically written.
The three dictionaries here are primitive book-column, count, and boundary inputs. -/
theorem issued_socket_owner (positive : 0 < A.sites) (m : Memory w) (low : A.Lower w) (fit : A.finish < 2^w)
    (sites : Fin A.sites → Site) (f : ∀ i, DescentTerminalLocalPortBook.Room (sites i) G V M K)
    (labels : ∀ i,(sites i).Name → Word a) (refs : ∀ i,(sites i).Arg → Word a)
    (wp : 0<W) (perSite : ∀ i,(sites i).rows q ≤ W)
    (paid : purchased W (counts (q:=q) sites) ≤ A.rows) (counter : A.rows+W < 2^w)
    (boundaryRoom : A.boundaries+(A.rows+1) ≤ A.start)
    (issued : Book.Issued A.parts (fun i => issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM : ∀ j : Fin (Book.Bytes G V M K a),A.countTable.read m (j.val : Word w) = DescentTerminalLocalPortBook.countTable q j)
    (boundaryROM : ∀ j : Fin (A.rows+1),m (A.boundaries+j.val) = (DescentTerminalBinPackCheap.boundaries w W A.rows)[j.val]'j.isLt)
    (r : Fin A.rows) :
    A.row.locate.Facts sites r perSite (A.siteSockets positive m) := by
  have prior := A.issued_owner m low fit sites f labels refs wp perSite paid counter boundaryRoom
    issued countsROM boundaryROM r
  have active := sockets_cursor_read A positive m low fit 10 (by decide) (r.val : Word w)
  have owner := sockets_cursor_read A positive m low fit 11 (by decide) (r.val : Word w)
  have offset := sockets_cursor_read A positive m low fit 12 (by decide) (r.val : Word w)
  refine ⟨active.trans prior.1,?_⟩
  intro i j used
  have value := prior.2 i j used
  exact ⟨owner.trans value.1,offset.trans value.2⟩

end
end Hierarchy.DescentTerminalRowArena.Arena

end OAI
