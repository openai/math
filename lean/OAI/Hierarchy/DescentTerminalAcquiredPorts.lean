import OAI.Hierarchy.DescentTerminalPreflightPortFrames

namespace OAI
/-! # The terminal scatter controls from the two predecessor width writers -/
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
set_option maxHeartbeats 900000

private theorem maskStartRoom {blocks w : ℕ} (V : Home.Format) (cfg : DescentTerminalCompiledPrefix.Shape)
    (I : Input) (R : MaskAllocation.Channels blocks) (start : ℕ) (space : last V cfg I R start < 2^w) :
    start < 2^w := by
  have above : start ≤ afterMeter V cfg R start := by
    change start ≤ start+_+_+_+_+3
    omega
  have stage := stages cfg I (afterMeter V cfg R start)
  exact above.trans_lt (((rowArena cfg I (afterMeter V cfg R start)).start_le 22).trans_lt
    (stage.1.trans_lt (stage.2.1.trans_lt (stage.2.2.1.trans_lt
      (stage.2.2.2.1.trans_lt (stage.2.2.2.2.trans_lt space))))))

private theorem readsRows {q p w n n' : ℕ} (rows : n = n') (layout : DescentTerminalDenseHeaderRAM.Layout)
    (stream : List (Profile q p)) (m : Memory w)
    (read : DescentTerminalDenseHeaderRAM.Reads layout (padded (n:=n) stream) m) :
    DescentTerminalDenseHeaderRAM.Reads layout (padded (n:=n') stream) m := by
  subst n'
  exact read

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
variable (head empty : ℕ) (bookMem : Memory w) (values : ℕ→ℕ)
    (short : vertices*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
local notation "controlled" => (x.controls begin_).after values (Book.expression (x.parts begin_)) bookMem
local notation "cabled" => (x.cables begin_ peer oldCable).final q grain controlled
local notation "original" => x.afterWidths begin_ q grain peer oldCable controlled
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

/-- All candidate-dependent source facts precede the public-width scan. The earlier cable
fields are the two outputs of Counter.cable_fields on the physical signed cable pages. -/
def acquired_ports_width_after (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid actors oldCable peer total modulo homes boundary)
    (earlyRom : rom+extent q grain≤x.bookEnd begin_)
    (full : front+DescentTerminalPublicIdentity.total K W q piece codes raw cfg.packets≤ start)
    (space : last V cfg I_ R_ start<2^w)
    (rows : cfg.terminal.rows=K*W) (draftRows : x.paidRows=K*W)
    (edges : ∀e,grain∣N.width e) (pins : ∀z,grain∣bw z)
    (sorted : Sorted roster) (covers : ∀e,0<N.width e→home (N.dst e)∈present roster (home (N.src e)) ∧
      home (N.src e)∈present roster (home (N.dst e)))
    (perSite : ∀u,(sites_ u).rows q≤W) (purchasedRows : purchased W (counts (q:=q) sites_)≤x.paidRows)
    (counter : x.paidRows+W<2^w) (high : 2<2^w) (hosts : H<2^w) (sockets : H*x.degree<2^w)
    (book : Book.Issued (x.parts begin_) (fun u=>issue (sites_ u) (shelves u) (labels u) (refs u)) bookMem)
    (countWords : ∀i:Fin (Book.Bytes nG nV nM nA bits),total.read bookMem (i.val:Computability.VPVNP.BurstRAM.Word w)=countTable q i)
    (boundaryWords : ∀i:Fin (x.paidRows+1),bookMem (boundary+i.val)=(DescentTerminalBinPackCheap.boundaries w W x.paidRows)[i.val])
    (tableWords : ∀j<extent q grain,bookMem (rom+j)=DescentTerminalDenseHeaderBoot.back w q grain j)
    (activeStrips : 0<x.strips) (sameRows : x.headerRows=limit) (peerRows : H*x.degree≤peer.size)
    (peerData : ∀(i : Fin H) (j : Fin x.degree),bookMem (peer.base+(i.val*x.degree+j.val))=
      (DescentPackedColony.target (roster i j) : Computability.VPVNP.BurstRAM.Word w))
    (cohorts : Fin H→ℕ) (cohortCap : ∀i,cohorts i≤(x.publicWidths begin_).maxCohorts)
    (census : ∀i : Fin H,bookMem ((x.census begin_).base+i.val)=(cohorts i : Computability.VPVNP.BurstRAM.Word w))
    (mass : ∀i,cohorts i*x.publicGrains=DescentTerminalExteriorHeaders.siteMass N home i/grain)
    (ci : (ipt (H*H)).length≤limit) (pu : (ept H).length≤limit)
    (cableWords : DescentTerminalDenseHeaderRAM.Reads privateReader
        (padded (n:=x.headerRows) (ipt (H*H))) cabled)
    (cableOffsets : ∀j : Fin (H*x.degree),(x.cables begin_ peer oldCable).printer.prefix.read cabled (j.val:Computability.VPVNP.BurstRAM.Word w)=
        ((passed q grain (slotCount (p:=grain) roster N home) (j.val+1)).length:Computability.VPVNP.BurstRAM.Word w))
    (later : Memory w) (headerKept : ∀j,litBase≤j→j<start→later j=source_ j)
    (cableKept : ∀i u,((I_).cable i).read later u=((I_).cable i).read source_ u)
    (publicKept : ∀i u,((I_).exterior i).read later u=((I_).exterior i).read source_ u) :
    { _cols : ControlColumns cfg.terminal (plan_).emit (eventsIn later) N home native ext nodes ops r hp birth wp hq bins banks_ //
      DescentTerminalDenseHeaderRAM.Reads (plan_).emit.plane.header (padded (n:=limit) (ipt (H*H))) later } := by
  have word := maskStartRoom V cfg I_ R_ start space
  have publicTape := DescentTerminalPublicWidthTape.tape_eq N home native ext nodes ops hp edges pins q hq
    (fun i=>DescentTerminalExteriorHeaders.siteMass N home i/grain) (fun _=>rfl)
  have privateTape := slot_stream roster N home native ext nodes ops hp edges pins sorted covers q
  let priv := (bodyPlane cfg I_ base_).header
  let pub := publicHeader cfg I_ base_
  have facts := x.port_frames begin_ q grain peer oldCable total modulo homes boundary bookMem values
    paid actors boot word activeStrips N home roster rom
    ![priv.rem,priv.whole,priv.index,priv.control] ![pub.rem,pub.whole,pub.index,pub.control]
    (ipt (H*H)) (ept H) (Nat.mul_pos hq hp) earlyRom tableWords peerRows peerData cohorts cohortCap
    census mass publicTape (by simpa only [sameRows] using pu) cableWords cableOffsets
  have earlier := x.book_at_ports begin_ q grain peer oldCable total modulo homes boundary bookMem values
    paid actors boot word activeStrips _ W book countWords boundaryWords
  obtain ⟨measured,privateWords,publicWords⟩:=facts
  obtain ⟨issued,limits,bounds⟩:=earlier
  have litEq := congrArg (fun n => DescentTerminalHeaderDraft.litMem litBase n original) draftRows
  rw [litEq] at measured issued limits
  have bounds' : ∀i : Fin (x.paidRows+1),before_ (boundary+i.val)=
      (DescentTerminalBinPackCheap.boundaries w W x.paidRows)[i.val] := by
    intro i
    exact (congrFun litEq _).symm.trans (bounds i)
  obtain ⟨_,_,_,_,ec,ct,tl,_,_⟩:=x.layers begin_
  have draftFit := x.fits_draft begin_ word paid actors oldCable peer total modulo homes boundary boot
  have romBefore := earlyRom.trans (ec.trans (ct.trans tl))
  have low := x.ports_before begin_ rom q grain peer oldCable total modulo homes boundary cfg other romBefore
  have pos : 0<w := by
    by_contra! h
    have zero : w=0 := by omega
    simp [zero] at high
  have litLow : litBase+4*DescentTerminalHeaderDraft.span (K*W)≤(A_).start := by
    rw [←draftRows]
    rfl
  have before := HeaderColumns.incoming_width A_ L_ x.degree litBase (K*W) original draftFit.1
    litLow pos privateReader (by change ∀j,((I_).cable j).base+((I_).cable j).size≤litBase;exact low.1)
    privateWords
  have after : DescentTerminalDenseHeaderRAM.Reads (plan_).emit.plane.header
      (padded (n:=x.headerRows) (ipt (H*H))) later := by
    apply HeaderColumns.five_reads before
    intro j u
    have current : HeaderColumns.inputBanks (plan_).emit.plane.header j=(I_).cable j := by
      fin_cases j <;> rfl
    rw [current]
    exact cableKept j u
  refine ⟨?_,readsRows sameRows _ _ _ after⟩
  exact x.printed_ports_after begin_ rom q piece W K codes front peer oldCable total modulo homes boundary
    cfg V other T vertices B roster N home native ext nodes ops hp hq wp r birth shelves labels refs bins
    head empty original short paid actors boot (earlyRom.trans (ec.trans (ct.trans tl))) full space
    rows draftRows edges pins sorted covers perSite purchasedRows counter high hosts sockets
    issued limits bounds' measured
    (by change ((List.ofFn (slotCount (p:=grain) roster N home)).flatMap
          (DescentTerminalGrainProfiles.rows q grain)).length ≤ limit
        rw [privateTape];exact ci)
    (by rw [publicTape];exact pu) ci pu
    (readsRows sameRows privateReader _ _ privateWords) (readsRows sameRows publicReader _ _ publicWords)
    later headerKept cableKept publicKept

def acquired_ports_after (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid actors oldCable peer total modulo homes boundary)
    (earlyRom : rom+extent q grain≤x.bookEnd begin_)
    (full : front+DescentTerminalPublicIdentity.total K W q piece codes raw cfg.packets≤ start)
    (space : last V cfg I_ R_ start<2^w)
    (rows : cfg.terminal.rows=K*W) (draftRows : x.paidRows=K*W)
    (edges : ∀e,grain∣N.width e) (pins : ∀z,grain∣bw z)
    (sorted : Sorted roster) (covers : ∀e,0<N.width e→home (N.dst e)∈present roster (home (N.src e)) ∧
      home (N.src e)∈present roster (home (N.dst e)))
    (perSite : ∀u,(sites_ u).rows q≤W) (purchasedRows : purchased W (counts (q:=q) sites_)≤x.paidRows)
    (counter : x.paidRows+W<2^w) (high : 2<2^w) (hosts : H<2^w) (sockets : H*x.degree<2^w)
    (book : Book.Issued (x.parts begin_) (fun u=>issue (sites_ u) (shelves u) (labels u) (refs u)) bookMem)
    (countWords : ∀i:Fin (Book.Bytes nG nV nM nA bits),total.read bookMem (i.val:Computability.VPVNP.BurstRAM.Word w)=countTable q i)
    (boundaryWords : ∀i:Fin (x.paidRows+1),bookMem (boundary+i.val)=(DescentTerminalBinPackCheap.boundaries w W x.paidRows)[i.val])
    (tableWords : ∀j<extent q grain,bookMem (rom+j)=DescentTerminalDenseHeaderBoot.back w q grain j)
    (activeStrips : 0<x.strips) (sameRows : x.headerRows=limit) (peerRows : H*x.degree≤peer.size)
    (peerData : ∀(i : Fin H) (j : Fin x.degree),bookMem (peer.base+(i.val*x.degree+j.val))=
      (DescentPackedColony.target (roster i j) : Computability.VPVNP.BurstRAM.Word w))
    (cohorts : Fin H→ℕ) (cohortCap : ∀i,cohorts i≤(x.publicWidths begin_).maxCohorts)
    (census : ∀i : Fin H,bookMem ((x.census begin_).base+i.val)=(cohorts i : Computability.VPVNP.BurstRAM.Word w))
    (mass : ∀i,cohorts i*x.publicGrains=DescentTerminalExteriorHeaders.siteMass N home i/grain)
    (ci : (ipt (H*H)).length≤limit) (pu : (ept H).length≤limit)
    (cableWords : DescentTerminalDenseHeaderRAM.Reads privateReader
        (padded (n:=x.headerRows) (ipt (H*H))) cabled)
    (cableOffsets : ∀j : Fin (H*x.degree),(x.cables begin_ peer oldCable).printer.prefix.read cabled (j.val:Computability.VPVNP.BurstRAM.Word w)=
        ((passed q grain (slotCount (p:=grain) roster N home) (j.val+1)).length:Computability.VPVNP.BurstRAM.Word w))
    (later : Memory w) (headerKept : ∀j,litBase≤j→j<start→later j=source_ j)
    (cableKept : ∀i u,((I_).cable i).read later u=((I_).cable i).read source_ u)
    (publicKept : ∀i u,((I_).exterior i).read later u=((I_).exterior i).read source_ u) :
    ControlColumns cfg.terminal (plan_).emit (eventsIn later) N home native ext nodes ops r hp birth wp hq bins banks_ := by
  exact (x.acquired_ports_width_after begin_ rom q piece W K codes front peer oldCable total modulo homes boundary
    cfg V other T vertices B roster N home native ext nodes ops hp hq wp r birth shelves labels refs bins
    head empty bookMem values short paid actors boot earlyRom full space rows draftRows edges pins sorted covers
    perSite purchasedRows counter high hosts sockets book countWords boundaryWords tableWords activeStrips
    sameRows peerRows peerData cohorts cohortCap census mass ci pu cableWords cableOffsets later
    headerKept cableKept publicKept).1

def acquired_ports (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid actors oldCable peer total modulo homes boundary)
    (earlyRom : rom+extent q grain≤x.bookEnd begin_)
    (full : front+DescentTerminalPublicIdentity.total K W q piece codes raw cfg.packets≤ start)
    (space : last V cfg I_ R_ start<2^w)
    (rows : cfg.terminal.rows=K*W) (draftRows : x.paidRows=K*W)
    (edges : ∀e,grain∣N.width e) (pins : ∀z,grain∣bw z)
    (sorted : Sorted roster) (covers : ∀e,0<N.width e→home (N.dst e)∈present roster (home (N.src e)) ∧
      home (N.src e)∈present roster (home (N.dst e)))
    (perSite : ∀u,(sites_ u).rows q≤W) (purchasedRows : purchased W (counts (q:=q) sites_)≤x.paidRows)
    (counter : x.paidRows+W<2^w) (high : 2<2^w) (hosts : H<2^w) (sockets : H*x.degree<2^w)
    (book : Book.Issued (x.parts begin_) (fun u=>issue (sites_ u) (shelves u) (labels u) (refs u)) bookMem)
    (countWords : ∀i:Fin (Book.Bytes nG nV nM nA bits),total.read bookMem (i.val:Computability.VPVNP.BurstRAM.Word w)=countTable q i)
    (boundaryWords : ∀i:Fin (x.paidRows+1),bookMem (boundary+i.val)=(DescentTerminalBinPackCheap.boundaries w W x.paidRows)[i.val])
    (tableWords : ∀j<extent q grain,bookMem (rom+j)=DescentTerminalDenseHeaderBoot.back w q grain j)
    (activeStrips : 0<x.strips) (sameRows : x.headerRows=limit) (peerRows : H*x.degree≤peer.size)
    (peerData : ∀(i : Fin H) (j : Fin x.degree),bookMem (peer.base+(i.val*x.degree+j.val))=
      (DescentPackedColony.target (roster i j) : Computability.VPVNP.BurstRAM.Word w))
    (cohorts : Fin H→ℕ) (cohortCap : ∀i,cohorts i≤(x.publicWidths begin_).maxCohorts)
    (census : ∀i : Fin H,bookMem ((x.census begin_).base+i.val)=(cohorts i : Computability.VPVNP.BurstRAM.Word w))
    (mass : ∀i,cohorts i*x.publicGrains=DescentTerminalExteriorHeaders.siteMass N home i/grain)
    (ci : (ipt (H*H)).length≤limit) (pu : (ept H).length≤limit)
    (cableWords : DescentTerminalDenseHeaderRAM.Reads privateReader
        (padded (n:=x.headerRows) (ipt (H*H))) cabled)
    (cableOffsets : ∀j : Fin (H*x.degree),(x.cables begin_ peer oldCable).printer.prefix.read cabled (j.val:Computability.VPVNP.BurstRAM.Word w)=
        ((passed q grain (slotCount (p:=grain) roster N home) (j.val+1)).length:Computability.VPVNP.BurstRAM.Word w)) :
    ControlColumns cfg.terminal (plan_).emit events_ N home native ext nodes ops r hp birth wp hq bins banks_ := by
  exact x.acquired_ports_after begin_ rom q piece W K codes front peer oldCable total modulo homes boundary
    cfg V other T vertices B roster N home native ext nodes ops hp hq wp r birth shelves labels refs bins
    head empty bookMem values short paid actors boot earlyRom full space rows draftRows edges pins sorted covers
    perSite purchasedRows counter high hosts sockets book countWords boundaryWords tableWords activeStrips
    sameRows peerRows peerData cohorts cohortCap census mass ci pu cableWords cableOffsets source_
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
