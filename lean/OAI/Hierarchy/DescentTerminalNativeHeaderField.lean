import OAI.Hierarchy.DescentTerminalHeaderSourceWords

namespace OAI
/-! # The paid header event scatter from original Book, peer, width-prefix and decoded source data -/
namespace Hierarchy.DescentTerminalHeaderDraft
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalHeaderSockets DescentTerminalPaidHeaderEvents DescentTerminalRowArena
open DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack DescentTerminalSpanBook
open DescentTerminalChipSource DescentTerminalGrainProfiles DescentTerminalCableOrder DescentTerminalWidthRowsRAM
open DescentKernelHistory hiding Word
open DescentSortedRoster Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts
open ThreeFlat.Routing
open DescentTerminalHeaderGroups DescentTerminalDenseHeader DescentTerminalDenseWindow
open DescentTerminalDenseGraphRead DescentTerminalPublicGroup
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable (A:Arena) {deg D p q W K w:ℕ} (L:DescentTerminalHeaderSockets.Layout) (R:Fin A.sites→Fin D→Option (Fin A.sites))
    {P Tag:Type} [Fintype P] {bw:P→ℕ} (N:Network deg P bw) (home:N.Site→Fin A.sites)
    (native:N.Edge↪Fin (Fintype.card N.Edge)) (ext:P↪ℕ) (nodes:N.Site↪ℕ) (ops:∀v,Boundary N v↪ℕ)
    (hp:0<p) (hq:0<q) (edges:∀e,p∣N.width e) (ports:∀z,p∣bw z)
    (sorted:Sorted R) (covers:∀e,0<N.width e→home (N.dst e)∈present R (home (N.src e)) ∧
      home (N.src e)∈present R (home (N.dst e)))
    (r:∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (birth:∀v,(r v).Node↪ℕ)
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

variable (prev:Earlier (p:=p) (q:=q) A L R N home m)
    (high:2<2^w) (hosts:A.sites<2^w) (area:A.sites*D<2^w)
    (cRoom:(tape (groups:=A.sites*D) q p (slotCount (p:=p) R N home)).length<2^w)
    (pRoom:(tape (groups:=A.sites) q p (fun v:Fin A.sites=>DescentTerminalExteriorHeaders.siteMass N home v/p)).length<2^w)
    (length:A.rows=K*W)
    (bins:Bins (W:=W) (q:=q) (DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth)≤K)

variable {rawRows:ℕ} (mem:Memory w) (cable outer:DescentTerminalDenseHeaderRAM.Layout)
    (privateRows:
      let graphOrder := order N home native p ext nodes ops
      let packetsBefore := DescentTerminalHeaderGroups.stream (p:=p) N home native ext nodes ops q hp
      ∀(t:ℕ) (_:t<A.sites*A.sites) (live:0<pairMass N home t),
      let g:=selected N home native ext nodes ops hp t live
      ∀k:Fin (poolBatchCount (Fintype.card (Order.At graphOrder g.site g.group)) q),
        let z:DescentTerminalDenseCableFetch.Packet N graphOrder q:=⟨g.site,g.other,g.group,g.near,k⟩
        mem (cable.index.base+((packetsBefore t).length+k.val))=(DescentTerminalDenseCableFetch.index N home native ext nodes ops z:Word w) ∧
        mem (cable.control.base+((packetsBefore t).length+k.val))=((formatIndex q p
          (DescentTerminalDenseCableFetch.fmt N home native ext nodes ops (Nat.mul_pos hq hp) z)).val:Word w))
    (publicRows:
      let graphOrder := order N home native p ext nodes ops
      let packetsBefore := DescentTerminalExteriorHeaders.stream (p:=p) (q:=q) N home native ext nodes ops
      ∀(i:Fin A.sites) (g:Order.Group graphOrder i) (_:g.val=none) (k:Fin (poolBatchCount (Fintype.card (Order.At graphOrder i g)) q)),
      let len:=groupLengths N graphOrder i g
      let small:∀z,len z≤p:=fun z=>by dsimp [len,groupLengths];cases ((Order.inGroup graphOrder i g).symm z).val <;> exact Nat.min_le_left ..
      mem (outer.index.base+((packetsBefore i.val).length+k.val))=((DescentTerminalDenseWindow.first len q (DescentTerminalPublicGroup.siteBase N home i) k.val/(q*p):ℕ):Word w) ∧
      mem (outer.control.base+((packetsBefore i.val).length+k.val))=((formatIndex q p (format len (Nat.mul_pos hq hp) small
        (DescentTerminalPublicGroup.siteBase N home i) k.val)).val:Word w))

local notation "sites" => DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth
local notation "rows" => K*W

include hq edges ports sorted covers ok wp fit paid counter boundary book countRom boundRom prev high hosts area
  cRoom pRoom length privateRows publicRows in
def native_field (format:Bool) (s:Fixed) (dest:Bank) (src blank capacity:ℕ) (fixed:s.Reads mem rows)
    (kept:∀j,A.finish≤j→j<stop A→mem j=data A L D m j)
    (cableN:(tape q p (slotCount (p:=p) R N home)).length≤capacity) (publicN:(tape q p (fun v:Fin A.sites=>DescentTerminalExteriorHeaders.siteMass N home v/p)).length≤capacity) (word:capacity≤2^w)
    (cin:capacity≤(fieldBank cable format).size) (pin:capacity≤(fieldBank outer format).size)
    (space:rows<dest.size)
    (readable:(DescentTerminalHeaderScatter.stage
      (DescentTerminalScatterChip.dest (wires s (output A) (fieldBank cable format) (fieldBank outer format)) dest.base (dest.base+rows))
      (DescentTerminalScatterChip.datum (wires s (output A) (fieldBank cable format) (fieldBank outer format)) (if format then 0 else rawRows+2))
      s.lane).Fits w dest.base) :
    DescentTerminalEmitter.Header.Emits (header rows s (output A) (fieldBank cable format) (fieldBank outer format)
      dest src (if format then 0 else rawRows+2) blank) mem (DescentTerminalScatterColumns.fixed sites wp bins)
      (fieldWord (rawRows:=rawRows) N home native ext nodes ops r hp birth hq format) := by
  have actual (a:GroupRow (q:=q) sites):=
    source_words (rawRows:=rawRows) N home native ext nodes ops r hp birth hq mem cable outer
      privateRows publicRows format a
      (event_bound R N home native ext nodes ops hp hq edges ports sorted covers r birth a cableN publicN) word cin pin
  exact graph_emit (W:=W) (K:=K) (q:=q) (p:=p) (w:=w) (deg:=deg) (D:=D) (P:=P) (Tag:=Tag)
    (bw:=bw) (nG:=nG) (nV:=nV) (nM:=nM) (nA:=nA) (bits:=bits)
    (A:=A) (L:=L) (R:=R) (N:=N) (home:=home) (native:=native) (ext:=ext)
    (nodes:=nodes) (ops:=ops) (hp:=hp) (hq:=hq) (edges:=edges) (ports:=ports) (sorted:=sorted)
    (covers:=covers) (r:=r) (birth:=birth) (m:=m) (ok:=ok) (shelves:=shelves) (labels:=labels)
    (refs:=refs) (wp:=wp) (fit:=fit) (paid:=paid) (counter:=counter) (boundary:=boundary) (book:=book)
    (countRom:=countRom) (boundRom:=boundRom) (prev:=prev) (high:=high) (hosts:=hosts) (area:=area)
    (cRoom:=cRoom) (pRoom:=pRoom) (length:=length) (bins:=bins)
    s (fieldBank cable format) (fieldBank outer format) dest src _ blank mem _ fixed kept
    (fun a=>(actual a).1) (fun a=>(actual a).2) space readable

end
end Hierarchy.DescentTerminalHeaderDraft

end OAI
