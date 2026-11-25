import OAI.Hierarchy.DescentTerminalHeaderEmit

namespace OAI
/-! # Actual bounded scatter from the original draft and a later preserved snapshot -/
namespace Hierarchy.DescentTerminalHeaderDraft
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalHeaderSockets DescentTerminalPaidHeaderEvents DescentTerminalRowArena
open DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack DescentTerminalSpanBook
open DescentTerminalChipSource DescentTerminalGrainProfiles DescentTerminalCableOrder DescentTerminalWidthRowsRAM
open DescentSortedRoster Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts
open ThreeFlat.Routing
open scoped Classical Fin.CommRing BigOperators
noncomputable section
attribute [local irreducible] DescentTerminalWidthRowsRAM.tape DescentTerminalExteriorHeaders.siteMass
  DescentTerminalGrainProfiles.slotCount

variable (A:Arena) {deg D p q W K w:ℕ} (L:DescentTerminalHeaderSockets.Layout) (R:Fin A.sites→Fin D→Option (Fin A.sites))
    {P Tag:Type} [Fintype P] {bw:P→ℕ} (N:Network deg P bw) (home:N.Site→Fin A.sites)
    (native:N.Edge↪Fin (Fintype.card N.Edge)) (ext:P↪ℕ) (nodes:N.Site↪ℕ) (ops:∀v,DescentKernelHistory.Boundary N v↪ℕ)
    (hp:0<p) (hq:0<q) (edges:∀e,p∣N.width e) (ports:∀z,p∣bw z)
    (sorted:Sorted R) (covers:∀e,0<N.width e→home (N.dst e)∈present R (home (N.src e)) ∧
      home (N.src e)∈present R (home (N.dst e)))
    (r:∀v,DescentKernelHistory.Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (birth:∀v,(r v).Node↪ℕ)
local notation "G" => order N home native p ext nodes ops
local notation "sites" => DescentTerminalBundleRows.site G r hp birth
local notation "cut" => cableOffset (p:=p) R N home q
local notation "pub" => publicOffset (p:=p) N home q
local notation "cc" => slotCount (p:=p) R N home
local notation "pc" => fun v=>DescentTerminalExteriorHeaders.siteMass N home v/p
local notation "event" => Slots.emitted (H:=A.sites) (q:=q) (W:=W) (K:=K) («sites»:=sites)
variable {nG nV nM nA bits:ℕ} (m:Memory w) (ok:Room A L D w)
    (shelves:∀v,DescentTerminalLocalPortBook.Room
      (DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v) nG nV nM nA)
    (labels:∀v,(DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v).Name→Word bits)
    (refs:∀v,(DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v).Arg→Word bits)
    (wp:0<W) (fit:∀v,(DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v).rows q≤W)
    (paid:purchased W (counts (q:=q) (DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth))≤A.rows)
    (counter:A.rows+W<2^w) (boundary:A.boundaries+(A.rows+1)≤A.start)
    (book:Book.Issued A.parts (fun v=>issue
      (DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v)
      (shelves v) (labels v) (refs v)) m)
    (countRom:∀j:Fin (Book.Bytes nG nV nM nA bits),A.countTable.read m (j.val:Word w)=countTable q j)
    (boundRom:∀j:Fin (A.rows+1),m (A.boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries w W A.rows)[j.val])
local notation "rows" => K*W
set_option quotPrecheck false in
local notation "first" => fun a:GroupRow (q:=q) sites=>DescentTerminalScatterRows.srcStart N home native ext nodes ops r hp birth a+a.2.2.val
set_option quotPrecheck false in
local notation "onPublic" => fun a:GroupRow (q:=q) sites=>
  ((DescentTerminalGraphPositions.Order.groups G a.1).symm a.2.1).val.isNone

variable (prev:Earlier (p:=p) (q:=q) A L R N home m)
    (high:2<2^w) (hosts:A.sites<2^w) (area:A.sites*D<2^w)
    (length:A.rows=K*W)


private theorem retained_column {E : Type} (A : Arena) {n w : ℕ} (len : A.rows=n)
    (old later : Memory w) (live : Fin n→Option E) (fromDraft wanted : Column→E→ℕ)
    (same : ∀c e,fromDraft c e=wanted c e)
    (kept : ∀j,A.finish≤j→j<stop A→later j=old j)
    (issued : ∀c (j:Fin A.rows),old (((output A).get c).base+j.val)=
      (((live (j.cast len)).elim 0 (fromDraft c) : ℕ) : Word w))
    (c : Column) (i : Fin n) :
    later (((output A).get c).base+i.val)=(((live i).elim 0 (wanted c) : ℕ) : Word w) := by
  have small:n≤2^Nat.clog 2 A.rows:=len.symm.le.trans (Nat.le_pow_clog (by decide) _)
  have above:A.finish≤((output A).get c).base+i.val:=by
    cases c <;> change A.finish≤A.finish+_+_ <;> omega
  have below:((output A).get c).base+n ≤ stop A:=by
    cases c <;> change A.finish+_*(2^Nat.clog 2 A.rows)+n≤A.finish+3*(2^Nat.clog 2 A.rows) <;> omega
  have row:=issued c (i.cast len.symm)
  have read:old (((output A).get c).base+i.val)=(((live i).elim 0 (fromDraft c) : ℕ) : Word w):=row
  refine (kept _ above ((Nat.add_lt_add_left i.isLt _).trans_le below)).trans (read.trans ?_)
  cases eq:live i with
  | none=>rfl
  | some e=>exact congrArg (fun value:ℕ=>(value:Word w)) (same c e)

private theorem graph_expected (c:Column) (a:GroupRow (q:=q) sites) :
    expected (A:=A) (q:=q) (p:=p) (N:=N) (home:=home) (native:=native) (ext:=ext)
      (nodes:=nodes) (ops:=ops) (r:=r) (hp:=hp) (birth:=birth) c a =
      answer sites first onPublic c a := by
  cases c with
  | active|source=>rfl
  | mode=>
    change (if ((DescentTerminalGraphPositions.Order.groups G a.1).symm a.2.1).val=none then 1 else 0) =
      (if ((DescentTerminalGraphPositions.Order.groups G a.1).symm a.2.1).val.isNone then 1 else 0)
    cases ((DescentTerminalGraphPositions.Order.groups G a.1).symm a.2.1).val <;> rfl

set_option maxHeartbeats 3200000 in
include hq edges ports sorted covers ok wp fit paid counter boundary book countRom boundRom prev high hosts area length in
def graph_emit
    (cRoom:(tape (groups:=A.sites*D) q p (slotCount (p:=p) R N home)).length<2^w)
    (pRoom:(tape (groups:=A.sites) q p (fun v:Fin A.sites=>DescentTerminalExteriorHeaders.siteMass N home v/p)).length<2^w)
    (bins:Bins (W:=W) (q:=q) (DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth)≤K)
    (s:Fixed) (inner outer dest:Bank) (src shift blank:ℕ) (mem:Memory w)
    (ans:GroupRow (q:=q) sites→Word w) (fixed:s.Reads mem rows)
    (kept:∀j,A.finish≤j→j<stop A→mem j=data A L D m j)
    (inside:∀(a:GroupRow (q:=q) sites),onPublic a=false→inner.read mem (first a:Word w)=ans a)
    (outside:∀(a:GroupRow (q:=q) sites),onPublic a=true→(shift:Word w)+outer.read mem (first a:Word w)=ans a)
    (space:rows<dest.size)
    (readable:(DescentTerminalHeaderScatter.stage
      (DescentTerminalScatterChip.dest (wires s (output A) inner outer) dest.base (dest.base+rows))
      (DescentTerminalScatterChip.datum (wires s (output A) inner outer) shift) s.lane).Fits w dest.base) :=
  emits (H:=A.sites) (q:=q) (W:=W) (K:=K) (w:=w)
    sites wp fit bins s (output A) inner outer dest src shift blank mem first onPublic ans fixed
    (length.symm.le.trans ((Nat.le_add_right A.rows W).trans counter.le))
    (fun c => by
      cases c <;> exact length.symm.le.trans (Nat.le_pow_clog (by decide : 1 < 2) A.rows))
    (retained_column (E:=GroupRow (q:=q) sites) A length (data A L D m) mem (event wp fit)
      (expected (A:=A) (q:=q) (p:=p) (N:=N) (home:=home) (native:=native) (ext:=ext)
        (nodes:=nodes) (ops:=ops) (r:=r) (hp:=hp) (birth:=birth))
      (answer sites first onPublic)
      (graph_expected (A:=A) (q:=q) (p:=p) (N:=N) (home:=home) (native:=native) (ext:=ext)
        (nodes:=nodes) (ops:=ops) (r:=r) (hp:=hp) (birth:=birth))
      kept
      (published (W:=W) (K:=K) (q:=q) (p:=p) (w:=w) (deg:=deg) (D:=D) (P:=P) (Tag:=Tag)
        (bw:=bw) (nG:=nG) (nV:=nV) (nM:=nM) (nA:=nA) (bits:=bits)
        (A:=A) (L:=L) (R:=R) (N:=N) (home:=home) (native:=native) (ext:=ext)
        (nodes:=nodes) (ops:=ops) (hp:=hp) (hq:=hq) (edges:=edges) (ports:=ports) (sorted:=sorted)
        (covers:=covers) (r:=r) (birth:=birth) (m:=m) (ok:=ok) (shelves:=shelves) (labels:=labels)
        (refs:=refs) (wp:=wp) (fit:=fit) (paid:=paid) (counter:=counter) (boundary:=boundary)
        (book:=book) (countRom:=countRom) (boundRom:=boundRom) prev high hosts area cRoom pRoom length))
    inside outside space readable


end
end Hierarchy.DescentTerminalHeaderDraft

end OAI
