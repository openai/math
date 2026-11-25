import OAI.Hierarchy.DescentTerminalRowPlan

namespace OAI
/-! # Early paid-site first and last cells of the actual compiled row plan -/
namespace Hierarchy.DescentTerminalRowPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w S W q G V M A a n : ℕ} (L : Layout) (sites : Fin S→Site) (f : ∀i,DescentTerminalLocalPortBook.Room (sites i) G V M A)
  (cable : ∀i,(sites i).Name→Word a) (args : ∀i,(sites i).Arg→Word a)
local notation "C" => counts (q:=q) sites
local notation "books" => fun i=>issue (sites i) (f i) (cable i) (args i)

theorem first_last (m : Memory w) (room : Room L S n w) (pos : 0<W) (max : ∀i,C i≤W)
    (whole : purchased W C≤n) (intRoom : n+W<2^w)
    (size : S≤L.books.size ∧ S≤L.counts.size ∧ S≤L.cursors.size)
    (countROMBelow : L.countTable.Fits w L.books.base) (endCaps : L.counts.base+S≤L.cursors.base)
    (tableLow : L.boundaries+(n+1)≤L.books.base) (endFile : L.boundaries+(n+1)≤L.cursors.base)
    (atomic : Book.Issued L.parts books m)
    (look : ∀i:Fin (Book.Bytes G V M A a),L.countTable.read m (i.val:Word w)=countTable q i)
    (boundary : ∀u:Fin (n+1),m (L.boundaries+u.val)=(DescentTerminalBinPackCheap.boundaries w W n)[u.val]'u.isLt)
    (i:Fin S) :
    header L S m (L.siteFirst.base+i.val)=(first W C i:Word w) ∧
    header L S m (L.siteLast.base+i.val)=(last W C i:Word w) := by
  have book:=Book.publish L.parts m L.books.base room.book room.bookEnd books atomic
  have countStart:=room.countData.2.2
  have earlyBook {a} (lo:a<L.books.base) : printed L S m a=m a:=
    DescentTerminalChipRuntime.image_low _ _ _ _ lo
  have fc (j:Fin S):L.books.read (printed L S m) (j.val:Word w)=((books j).bytes.val:Word w):=by
    have valid:=j.isLt.trans_le size.1
    simpa [Bank.read,Fin.val_cast_of_lt (valid.trans room.countData.2.1),Nat.mod_eq_of_lt valid,printed] using book.2.2 j
  have tableAt (j:Fin (Book.Bytes G V M A a)) : L.countTable.read (printed L S m) (j.val:Word w)=countTable q j:=by
    rw [←look]
    exact earlyBook (by have:=countROMBelow.2.2;have:=Nat.mod_lt (j.val:Word w).val countROMBelow.1;omega)
  have cur (j:Fin S) : sized L S m (L.counts.base+j.val)=(C j:Word w):=
    published sites f cable args L.books L.countTable L.counts.base _ fc tableAt j
  have spec := @DescentTerminalBinPackCheap.spec w S W pos L.counts.base L.boundaries L.cursors.base n C max whole
    endCaps endFile room.allocation intRoom
  have tableNow (k:Fin (n+1)) : sized L S m (L.boundaries+k.val)=(DescentTerminalBinPackCheap.boundaries w W n)[k.val]'k.isLt := by
    have lo := (Nat.add_lt_add_left k.isLt L.boundaries).trans_le tableLow
    have beforeCount : L.boundaries + k.val < L.counts.base := by omega
    exact (DescentTerminalChipRuntime.image_low (printed L S m) L.counts.base S (countRow L.books L.countTable)
      beforeCount).trans ((earlyBook lo).trans (boundary k))
  have issued : (DescentTerminalBinPackCheap.program w L.counts.base L.boundaries L.cursors.base S).Exec
      (sized L S m) (fillSegment L.cursors.base S (DescentTerminalBinPackCheap.file W L.cursors.base C) (sized L S m))
      (4 + 102*S) :=
    Procedure.Spec.exec spec _ ⟨cur,tableNow⟩
  have eq:=exec_unique _ (sized L S m) _ _ (DescentTerminalUniversalWrite.safe L.counts.base L.boundaries L.cursors.base _ room.allocation).1 issued
  have endAt : allocated L S m (L.cursors.base+i.val)=((first W C i+C i:ℕ):Word w):=by
    rw [show allocated L S m=_ from eq]
    simp [fillSegment,DescentTerminalBinPackCheap.file,i.isLt,cursor_step]
  have sizeAt : allocated L S m (L.counts.base+i.val)=(C i:Word w):=by
    rw [allocated,DescentTerminalUniversalWrite.image]
    simpa [fillSegment,not_le.mpr (show L.counts.base+i.val<L.cursors.base by omega)] using cur i
  exact DescentTerminalBinPackCheap.header_read L.siteFirst.base L.siteLast.base L.cursors L.counts C _ i
    (by change 0 < (sites i).rows q; simp [Site.rows]) room.endData room.sizes size.2.2 size.2.1 room.gap endAt sizeAt

end
end Hierarchy.DescentTerminalRowPlan

end OAI
