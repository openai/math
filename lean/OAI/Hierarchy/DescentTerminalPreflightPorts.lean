import OAI.Hierarchy.DescentTerminalPreflightEarlier

namespace OAI
/-! # The actual terminal scatter controls produced by the reached preflight -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalHeaderSockets DescentTerminalPaidHeaderEvents DescentTerminalRowArena
open DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack DescentTerminalSpanBook
open DescentTerminalChipSource DescentTerminalGrainProfiles DescentTerminalCableOrder DescentTerminalWidthRowsRAM
open DescentSortedRoster DescentKernelHistory Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts
open ThreeFlat.Routing
open DescentTerminalHeaderGroups DescentTerminalDenseHeader DescentTerminalDenseWindow DescentTerminalDenseGraphRead
open DescentTerminalEmitter DescentTerminalVertexFields DescentTerminalChipBootWords
open DescentTerminalCompiledPrefix DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalBinReaddress DescentTerminalScalarPadded DescentTerminalDenseHeaderBoot
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (begin_ rom q piece W K codes front : ℕ) (peer : Bank)
    (oldCable : Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (total modulo homes : Bank) (boundary : ℕ)
variable (cfg : DescentTerminalCompiledPrefix.Shape) (V : Home.Format)
    (other : Input) (T : RouteSources.Tables) (vertices B : ℕ)
local notation "I_" => x.reachedInput begin_ rom q piece W K codes front peer oldCable total modulo homes
                          boundary cfg V other T vertices B
local notation "grain" => W*piece
local notation "H" => x.scalar.shops
local notation "litBase" => x.literalBase begin_
local notation "A_" => x.draft begin_ total modulo homes boundary
local notation "L_" => x.eventInputs begin_ peer oldCable
local notation "R_" => x.channels begin_
local notation "start" => x.maskBase begin_
local notation "C_" => meter V R_ start
local notation "base_" => afterMeter V cfg R_ start
variable {deg w : ℕ} (roster : Fin x.scalar.shops→Fin x.degree→Option (Fin x.scalar.shops)) {P Tag : Type} [Fintype P] {bw : P→ℕ}
    (N : Network deg P bw) (home : N.Site→Fin x.scalar.shops) (native : N.Edge↪Fin (Fintype.card N.Edge))
    (ext : P↪ℕ) (nodes : N.Site↪ℕ) (ops : ∀v,Boundary N v↪ℕ)
    (hp : 0<W*piece) (hq : 0<q) (wp : 0<W)
    (r : ∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=W*piece) N v)) (birth : ∀v,(r v).Node↪ℕ)
local notation "G_" => order N home native grain ext nodes ops
local notation "sites_" => DescentTerminalBundleRows.site G_ r hp birth
variable {nG nV nM nA bits : ℕ}
variable (shelves:∀u,DescentTerminalLocalPortBook.Room ((DescentTerminalBundleRows.site (order N home native (W*piece) ext nodes ops) r hp birth) u) nG nV nM nA)
    (labels:∀u,((DescentTerminalBundleRows.site (order N home native (W*piece) ext nodes ops) r hp birth) u).Name → Computability.VPVNP.BurstRAM.Word bits) (refs:∀u,((DescentTerminalBundleRows.site (order N home native (W*piece) ext nodes ops) r hp birth) u).Arg → Computability.VPVNP.BurstRAM.Word bits)
    (bins : Bins (W:=W) (q:=q) (DescentTerminalBundleRows.site (order N home native (W*piece) ext nodes ops) r hp birth) ≤ K)
include shelves labels refs
variable (head empty : ℕ) (original : Memory w)
    (short : vertices*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
local notation "before_" => DescentTerminalHeaderDraft.litMem litBase (K*W) original
local notation "source_" => DescentTerminalHeaderDraft.data A_ L_ x.degree before_
local notation "O_" => registers V cfg R_ start head
local notation "row_" => rowArena cfg I_ base_
local notation "plan_" => AddressPlan.layout cfg I_ base_ O_
local notation "old_" => x.chipInput begin_ rom q grain peer oldCable total modulo homes boundary cfg other
local notation "originals" => Compact.ScalarLiterals.data q V.roles V.privateWords V.nodes V.addresses
        grain vertices W B cfg.terminal.pool hq (T.columns row_ (old_).sources) (T.value (fun _ _=>0))
local notation "load_" => input V cfg I_ R_ start head short originals
local notation "eventsIn" m => Suffix.events cfg plan_ (C_).layout ((row_).mount (load_ m))
local notation "events_" => eventsIn source_
local notation "limit" => cfg.terminal.plane.headerRows
local notation "raw" => cfg.terminal.plane.rawRows
local notation "ipt" => DescentTerminalHeaderGroups.stream (p:=grain) N home native ext nodes ops q hp
local notation "ept" => DescentTerminalExteriorHeaders.stream (q:=q) (p:=grain) N home native ext nodes ops
local notation "banks_" => chipBanks (K:=K) (W:=W) (q:=q) (p:=piece) codes (plan_).emit front empty
local notation "privateWidth" => (x.cables begin_ peer oldCable).printer.output
local notation "publicWidth" => (x.publicWidths begin_).widthLayout.output
local notation "privateReader" => DescentTerminalDenseHeaderBoot.layout q grain rom privateWidth
  (bodyPlane cfg I_ base_).header.rem (bodyPlane cfg I_ base_).header.whole
  (bodyPlane cfg I_ base_).header.index (bodyPlane cfg I_ base_).header.control
local notation "publicReader" => DescentTerminalDenseHeaderBoot.layout q grain rom publicWidth
  (publicHeader cfg I_ base_).rem (publicHeader cfg I_ base_).whole
  (publicHeader cfg I_ base_).index (publicHeader cfg I_ base_).control

/-- Use one native date for the row draft, the two width scans and the later two
scatters. The scalar decoder and all source-table values are fixed by the format. -/
def printed_ports_after (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid actors oldCable peer total modulo homes boundary)
    (earlyRom : rom+extent q grain≤litBase)
    (full : front+DescentTerminalPublicIdentity.total K W q piece codes raw cfg.packets≤ start)
    (space : last V cfg I_ R_ start<2^w)
    (rows : cfg.terminal.rows=K*W) (draftRows : x.paidRows=K*W)
    (edges : ∀e,grain∣N.width e) (pins : ∀z,grain∣bw z)
    (sorted : Sorted roster) (covers : ∀e,0<N.width e→home (N.dst e)∈present roster (home (N.src e)) ∧
      home (N.src e)∈present roster (home (N.dst e)))
    (perSite : ∀u,(sites_ u).rows q≤W) (purchasedRows : purchased W (counts (q:=q) sites_)≤x.paidRows)
    (counter : x.paidRows+W<2^w) (high : 2<2^w) (hosts : H<2^w) (sockets : H*x.degree<2^w)
    (book : Book.Issued (x.parts begin_) (fun u=>issue (sites_ u) (shelves u) (labels u) (refs u)) before_)
    (countWords : ∀i:Fin (Book.Bytes nG nV nM nA bits),total.read before_ (i.val:Computability.VPVNP.BurstRAM.Word w)=countTable q i)
    (boundaryWords : ∀i:Fin (x.paidRows+1),before_ (boundary+i.val)=(DescentTerminalBinPackCheap.boundaries w W x.paidRows)[i.val])
    (measured : DescentTerminalHeaderDraft.Earlier (p:=grain) (q:=q) A_ L_ roster N home before_)
    (cableSpan : (tape q grain (slotCount (p:=grain) roster N home)).length≤limit)
    (publicSpan : (tape q grain (fun z=>DescentTerminalExteriorHeaders.siteMass N home z/grain)).length≤limit)
    (ci : (ipt (H*H)).length≤limit) (pu : (ept H).length≤limit)
    (cableWords : DescentTerminalDenseHeaderRAM.Reads privateReader (padded (n:=limit) (ipt (H*H))) original)
    (publicWords : DescentTerminalDenseHeaderRAM.Reads publicReader (padded (n:=limit) (ept H)) original)
    (later : Memory w) (headerKept : ∀j,litBase≤j→j<start→later j=source_ j)
    (cableKept : ∀i u,((I_).cable i).read later u=((I_).cable i).read source_ u)
    (publicKept : ∀i u,((I_).exterior i).read later u=((I_).exterior i).read source_ u) :
    ControlColumns cfg.terminal (plan_).emit (eventsIn later) N home native ext nodes ops r hp birth wp hq bins banks_ := by
  have early := x.earlier begin_ rom q piece W K codes front peer oldCable total modulo homes boundary
    cfg V other T vertices B paid actors boot earlyRom full space
  obtain ⟨s0,s1,s2,s3,s4⟩:=stages cfg I_ base_
  have above : start≤base_ := by change start≤ start+_+_+_+_+3;omega
  have word := above.trans_lt (((row_).start_le 22).trans_lt
    (s0.trans_lt (s1.trans_lt (s2.trans_lt (s3.trans_lt (s4.trans_lt space))))))
  have frames := x.fits_draft begin_ word paid actors oldCable peer total modulo homes boundary boot
  obtain ⟨prior,ni,nf,blank,_⟩:=x.reached_headers begin_ rom q piece W K codes front peer oldCable
    total modulo homes boundary cfg V other T vertices B total modulo homes peer
  have sources := x.ports_before begin_ rom q grain peer oldCable total modulo homes boundary cfg other earlyRom
  apply HeaderColumns.native_ports_after A_ L_ roster N home native ext nodes ops hp hq wp r birth litBase
    original V cfg I_ R_ start head short originals shelves labels refs bins codes front empty
    edges pins sorted covers perSite purchasedRows counter frames.2 book countWords boundaryWords
    measured frames.1 high hosts sockets draftRows rows (x.draft_end begin_ total modulo homes boundary).le
    (by rw [←draftRows];rfl) (by simpa only [←draftRows] using prior) ni nf blank early space
    cableSpan publicSpan ci pu privateReader publicReader rfl rfl sources.1 sources.2 cableWords publicWords later (by simpa only [draft_end] using headerKept) cableKept publicKept

def printed_ports (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid actors oldCable peer total modulo homes boundary)
    (earlyRom : rom+extent q grain≤litBase)
    (full : front+DescentTerminalPublicIdentity.total K W q piece codes raw cfg.packets≤ start)
    (space : last V cfg I_ R_ start<2^w)
    (rows : cfg.terminal.rows=K*W) (draftRows : x.paidRows=K*W)
    (edges : ∀e,grain∣N.width e) (pins : ∀z,grain∣bw z)
    (sorted : Sorted roster) (covers : ∀e,0<N.width e→home (N.dst e)∈present roster (home (N.src e)) ∧
      home (N.src e)∈present roster (home (N.dst e)))
    (perSite : ∀u,(sites_ u).rows q≤W) (purchasedRows : purchased W (counts (q:=q) sites_)≤x.paidRows)
    (counter : x.paidRows+W<2^w) (high : 2<2^w) (hosts : H<2^w) (sockets : H*x.degree<2^w)
    (book : Book.Issued (x.parts begin_) (fun u=>issue (sites_ u) (shelves u) (labels u) (refs u)) before_)
    (countWords : ∀i:Fin (Book.Bytes nG nV nM nA bits),total.read before_ (i.val:Computability.VPVNP.BurstRAM.Word w)=countTable q i)
    (boundaryWords : ∀i:Fin (x.paidRows+1),before_ (boundary+i.val)=(DescentTerminalBinPackCheap.boundaries w W x.paidRows)[i.val])
    (measured : DescentTerminalHeaderDraft.Earlier (p:=grain) (q:=q) A_ L_ roster N home before_)
    (cableSpan : (tape q grain (slotCount (p:=grain) roster N home)).length≤limit)
    (publicSpan : (tape q grain (fun z=>DescentTerminalExteriorHeaders.siteMass N home z/grain)).length≤limit)
    (ci : (ipt (H*H)).length≤limit) (pu : (ept H).length≤limit)
    (cableWords : DescentTerminalDenseHeaderRAM.Reads privateReader (padded (n:=limit) (ipt (H*H))) original)
    (publicWords : DescentTerminalDenseHeaderRAM.Reads publicReader (padded (n:=limit) (ept H)) original) :
    ControlColumns cfg.terminal (plan_).emit events_ N home native ext nodes ops r hp birth wp hq bins banks_ := by
  exact x.printed_ports_after begin_ rom q piece W K codes front peer oldCable total modulo homes
    boundary cfg V other T vertices B roster N home native ext nodes ops hp hq wp r birth shelves labels refs bins
    head empty original short paid actors boot earlyRom full space rows draftRows edges pins sorted covers perSite
    purchasedRows counter high hosts sockets book countWords boundaryWords measured cableSpan publicSpan ci pu
    cableWords publicWords source_ (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
