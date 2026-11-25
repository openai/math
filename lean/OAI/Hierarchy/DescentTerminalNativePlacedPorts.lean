import OAI.Hierarchy.DescentTerminalPlacedControlColumns
import OAI.Hierarchy.DescentTerminalPlacedHeaderDates
import OAI.Hierarchy.DescentTerminalHeaderReady
import OAI.Hierarchy.DescentTerminalPlacedWidthRows
import OAI.Hierarchy.DescentTerminalEarlierWidthRows

namespace OAI
/-! # From the previous row plan and the two native width inputs to the chip ports -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalHeaderSockets DescentTerminalPaidHeaderEvents DescentTerminalRowArena
open DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack DescentTerminalSpanBook
open DescentTerminalChipSource DescentTerminalGrainProfiles DescentTerminalCableOrder DescentTerminalWidthRowsRAM
open DescentSortedRoster DescentKernelHistory Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts
open ThreeFlat.Routing
open DescentTerminalHeaderGroups DescentTerminalDenseHeader DescentTerminalDenseWindow DescentTerminalDenseGraphRead
open DescentTerminalEmitter DescentTerminalVertexFields DescentTerminalChipBootWords
open DescentTerminalBinReaddress DescentTerminalScalarPadded
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false

variable (A : Arena) {deg D piece q W K w : ℕ} (L : DescentTerminalHeaderSockets.Layout)
    (roster : Fin A.sites→Fin D→Option (Fin A.sites)) {P Tag : Type} [Fintype P] {bw : P→ℕ}
    (N : Network deg P bw) (home : N.Site→Fin A.sites) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (ext:P↪ℕ) (nodes:N.Site↪ℕ) (ops:∀v,Boundary N v↪ℕ)
local notation "grain" => W*piece
variable (hp : 0<W*piece) (hq : 0<q) (wp : 0<W)
    (r:∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=W*piece) N v)) (birth:∀v,(r v).Node↪ℕ)
local notation "G_" => order N home native grain ext nodes ops
local notation "sites_" => DescentTerminalBundleRows.site G_ r hp birth
local notation "count_" => K*W
variable (litBase : ℕ) (original : Memory w)
local notation "first_" => DescentTerminalHeaderDraft.litMem litBase count_ original
local notation "source_" => DescentTerminalHeaderDraft.data A L D first_
local notation "records" => DescentTerminalHeaderDraft.output A
local notation "fixed_" => DescentTerminalHeaderDraft.literals litBase count_

variable {blocks v B : ℕ} (V : Home.Format) (cfg : DescentTerminalCompiledPrefix.Shape)
    (I : Input) (R : MaskAllocation.Channels blocks) (start head : ℕ)
    (short : v*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤ B)
    (literal : Compact.Literals I.sources)
local notation "C_" => meter V R start
local notation "O_" => registers V cfg R start head
local notation "base_" => afterMeter V cfg R start
local notation "later_" => layout cfg I base_ O_
local notation "E_" => emitter cfg I base_
local notation "body" => bodyPlane cfg I base_
local notation "public_" => publicHeader cfg I base_
local notation "lo" => rowArena cfg I base_
local notation "load_" => input V cfg I R start head short literal
local notation "eventsIn" mem => Suffix.events cfg later_ (C_).layout ((lo).mount (load_ mem))
local notation "μ" => eventsIn source_
local notation "limit" => cfg.terminal.plane.headerRows
local notation "raw" => cfg.terminal.plane.rawRows
local notation "ipt" => DescentTerminalHeaderGroups.stream (p:=grain) N home native ext nodes ops q hp
local notation "ept" => DescentTerminalExteriorHeaders.stream (q:=q) (p:=grain) N home native ext nodes ops
local notation "cableTape" => tape q grain (slotCount (p:=grain) roster N home)
local notation "publicTape" => tape q grain (fun z=>DescentTerminalExteriorHeaders.siteMass N home z/grain)

variable {nG nV nM nA bits : ℕ}
variable (shelves:∀u,DescentTerminalLocalPortBook.Room ((DescentTerminalBundleRows.site (order N home native (W*piece) ext nodes ops) r hp birth) u) nG nV nM nA)
    (labels:∀u,((DescentTerminalBundleRows.site (order N home native (W*piece) ext nodes ops) r hp birth) u).Name → Computability.VPVNP.BurstRAM.Word bits) (refs:∀u,((DescentTerminalBundleRows.site (order N home native (W*piece) ext nodes ops) r hp birth) u).Arg → Computability.VPVNP.BurstRAM.Word bits)
    (bins : Bins (W:=W) (q:=q) (DescentTerminalBundleRows.site (order N home native (W*piece) ext nodes ops) r hp birth) ≤ K)
variable (codes front empty : ℕ)
local notation "banks_" => chipBanks (K:=K) (W:=W) (q:=q) (p:=piece) codes E_ front empty

/-- All computed words here have the same original native memory, including the
old licensed row plan, both width-pass input tables and the final chip control. -/
def native_ports_after (edges : ∀e,grain∣N.width e) (pins : ∀z,grain∣bw z)
    (sorted:Sorted roster) (covers:∀e,0<N.width e→home (N.dst e)∈present roster (home (N.src e)) ∧
      home (N.src e)∈present roster (home (N.dst e)))
    (perSite : ∀u,(sites_ u).rows q≤W) (paid : purchased W (counts (q:=q) sites_)≤A.rows)
    (counter:A.rows+W<2^w) (boundary:A.boundaries+(A.rows+1)≤A.start)
    (book:Book.Issued A.parts (fun u=>issue (sites_ u) (shelves u) (labels u) (refs u)) first_)
    (countRom:∀j:Fin (Book.Bytes nG nV nM nA bits),A.countTable.read first_ (j.val:Computability.VPVNP.BurstRAM.Word w)=countTable q j)
    (boundRom:∀j:Fin (A.rows+1),first_ (A.boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries w W A.rows)[j.val])
    (prev:DescentTerminalHeaderDraft.Earlier (p:=grain) (q:=q) A L roster N home first_)
    (ok : DescentTerminalHeaderDraft.Room A L D w) (high:2<2^w) (hosts:A.sites<2^w) (area:A.sites*D<2^w)
    (length : A.rows=count_) (rows : cfg.terminal.rows=count_)
    (saved : DescentTerminalHeaderDraft.stop A≤ start)
    (litLow : litBase+4*DescentTerminalHeaderDraft.span count_≤A.start)
    (prior : Uses fixed_ records I.sources)
    (ni : I.indexEvents=cfg.terminal.rows) (nf : I.formatEvents=cfg.terminal.rows)
    (blank : I.blank=(formatIndex q grain (DescentTerminalScalarPadded.blank q grain)).val)
    (early : Earlier cfg I base_ (C_).layout w) (space : last V cfg I R start<2^w)
    (cableSpan : (cableTape).length≤limit) (publicSpan : (publicTape).length≤limit)
    (ci : (ipt (A.sites*A.sites)).length≤limit) (pu : (ept A.sites).length≤limit)
    (oldCable oldPublic : DescentTerminalDenseHeaderRAM.Layout)
    (privateInputs : inputBanks oldCable=I.cable) (publicInputs : inputBanks oldPublic=I.exterior)
    (privateBefore : ∀j,(I.cable j).base+(I.cable j).size≤litBase)
    (publicBefore : ∀j,(I.exterior j).base+(I.exterior j).size≤litBase)
    (privateWords : DescentTerminalDenseHeaderRAM.Reads oldCable (padded (n:=limit) (ipt (A.sites*A.sites))) original)
    (publicWords : DescentTerminalDenseHeaderRAM.Reads oldPublic (padded (n:=limit) (ept A.sites)) original)
    (later : Memory w) (preserved : ∀j,litBase≤j→j<DescentTerminalHeaderDraft.stop A→later j=source_ j)
    (cableKept : ∀i u,(I.cable i).read later u=(I.cable i).read source_ u)
    (outerKept : ∀i u,(I.exterior i).read later u=(I.exterior i).read source_ u) :
    ControlColumns cfg.terminal E_ (eventsIn later) N home native ext nodes ops r hp birth wp hq bins banks_ := by
  refine ports cfg I base_ N home native ext nodes ops r hp birth wp hq bins fixed_ records
    codes front empty (eventsIn later) prior ni nf rows blank ?_
  intro fmt
  have capacity := suffix_room cfg I base_ (C_).layout O_ early space
  have width : limit<2^w := (Nat.le_add_left ..).trans_lt capacity.issuer.ext.endAt
  have pos : 0<w := by
    by_contra! h
    have zero : w=0 := by omega
    simp [zero] at high
  obtain ⟨live,kept⟩:=prepared_after V cfg I R start head short literal original early space
    A L D count_ litBase ok pos saved litLow later preserved fmt
  have lower : litBase≤ start := (Nat.le_add_right ..).trans (litLow.trans ((A.start_le 22).trans
    ((Nat.le_add_right A.finish (3*(2^Nat.clog 2 A.rows))).trans saved)))
  have privateAt := incoming_width A L D litBase count_ original ok litLow pos oldCable
    (by rw [privateInputs];exact privateBefore) privateWords
  have publicAt := incoming_width A L D litBase count_ original ok litLow pos oldPublic
    (by rw [publicInputs];exact publicBefore) publicWords
  have cableLater : DescentTerminalDenseHeaderRAM.Reads oldCable _ later :=
    five_reads privateAt (fun j u=>by rw [privateInputs];exact cableKept j u)
  have outerLater : DescentTerminalDenseHeaderRAM.Reads oldPublic _ later :=
    five_reads publicAt (fun j u=>by rw [publicInputs];exact outerKept j u)
  obtain ⟨cableReads,exteriorReads⟩:=dated_widths V cfg I R start head short literal later early space
    oldCable oldPublic _ _ privateInputs publicInputs (fun i=>(privateBefore i).trans lower)
    (fun i=>(publicBefore i).trans lower) cableLater outerLater
  obtain ⟨privateRows,publicRows⟩:=field_rows N home native ext nodes ops hp hq cfg I base_ (eventsIn later)
    capacity.issuer ci pu cableReads exteriorReads fmt
  have strong := native_room cfg I base_ fixed_ records (C_).layout prior early space fmt
  rw [rows] at strong
  have sized : limit≤DescentTerminalDataPlane.Arena.size limit := (DescentTerminalDataPlane.Arena.room limit).le
  exact DescentTerminalHeaderDraft.native_field (A:=A) (L:=L) (R:=roster) (N:=N) (home:=home)
    (native:=native) (ext:=ext) (nodes:=nodes) (ops:=ops) (hp:=hp) (hq:=hq) (edges:=edges) (ports:=pins)
    (sorted:=sorted) (covers:=covers) (r:=r) (birth:=birth) (m:=first_) (ok:=ok)
    (shelves:=shelves) (labels:=labels) (refs:=refs) (wp:=wp) (fit:=perSite) (paid:=paid)
    (counter:=counter) (boundary:=boundary) (book:=book) (countRom:=countRom) (boundRom:=boundRom)
    (prev:=prev) (high:=high) (hosts:=hosts) (area:=area) (cRoom:=cableSpan.trans_lt width)
    (pRoom:=publicSpan.trans_lt width) (length:=length) (bins:=bins)
    (rawRows:=raw) (mem:=phase V cfg I R start head short literal later fmt) (cable:=(body).header) (outer:=public_) (privateRows:=privateRows) (publicRows:=publicRows)
    fmt (fixed fixed_ cfg I base_) _ _ (if fmt then I.blank else 0) limit live kept
    cableSpan publicSpan width.le
    (by cases fmt <;> exact sized) (by cases fmt <;> exact sized) strong.1 strong.2

def native_ports (edges : ∀e,grain∣N.width e) (pins : ∀z,grain∣bw z)
    (sorted:Sorted roster) (covers:∀e,0<N.width e→home (N.dst e)∈present roster (home (N.src e)) ∧
      home (N.src e)∈present roster (home (N.dst e)))
    (perSite : ∀u,(sites_ u).rows q≤W) (paid : purchased W (counts (q:=q) sites_)≤A.rows)
    (counter:A.rows+W<2^w) (boundary:A.boundaries+(A.rows+1)≤A.start)
    (book:Book.Issued A.parts (fun u=>issue (sites_ u) (shelves u) (labels u) (refs u)) first_)
    (countRom:∀j:Fin (Book.Bytes nG nV nM nA bits),A.countTable.read first_ (j.val:Computability.VPVNP.BurstRAM.Word w)=countTable q j)
    (boundRom:∀j:Fin (A.rows+1),first_ (A.boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries w W A.rows)[j.val])
    (prev:DescentTerminalHeaderDraft.Earlier (p:=grain) (q:=q) A L roster N home first_)
    (ok : DescentTerminalHeaderDraft.Room A L D w) (high:2<2^w) (hosts:A.sites<2^w) (area:A.sites*D<2^w)
    (length : A.rows=count_) (rows : cfg.terminal.rows=count_)
    (saved : DescentTerminalHeaderDraft.stop A≤ start)
    (litLow : litBase+4*DescentTerminalHeaderDraft.span count_≤A.start)
    (prior : Uses fixed_ records I.sources)
    (ni : I.indexEvents=cfg.terminal.rows) (nf : I.formatEvents=cfg.terminal.rows)
    (blank : I.blank=(formatIndex q grain (DescentTerminalScalarPadded.blank q grain)).val)
    (early : Earlier cfg I base_ (C_).layout w) (space : last V cfg I R start<2^w)
    (cableSpan : (cableTape).length≤limit) (publicSpan : (publicTape).length≤limit)
    (ci : (ipt (A.sites*A.sites)).length≤limit) (pu : (ept A.sites).length≤limit)
    (oldCable oldPublic : DescentTerminalDenseHeaderRAM.Layout)
    (privateInputs : inputBanks oldCable=I.cable) (publicInputs : inputBanks oldPublic=I.exterior)
    (privateBefore : ∀j,(I.cable j).base+(I.cable j).size≤litBase)
    (publicBefore : ∀j,(I.exterior j).base+(I.exterior j).size≤litBase)
    (privateWords : DescentTerminalDenseHeaderRAM.Reads oldCable (padded (n:=limit) (ipt (A.sites*A.sites))) original)
    (publicWords : DescentTerminalDenseHeaderRAM.Reads oldPublic (padded (n:=limit) (ept A.sites)) original) :
    ControlColumns cfg.terminal E_ μ N home native ext nodes ops r hp birth wp hq bins banks_ := by
  exact native_ports_after A L roster N home native ext nodes ops hp hq wp r birth litBase original V cfg I R
    start head short literal shelves labels refs bins codes front empty edges pins sorted covers perSite paid
    counter boundary book countRom boundRom prev ok high hosts area length rows saved litLow prior ni nf blank
    early space cableSpan publicSpan ci pu oldCable oldPublic privateInputs publicInputs privateBefore publicBefore
    privateWords publicWords source_ (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns

end OAI
