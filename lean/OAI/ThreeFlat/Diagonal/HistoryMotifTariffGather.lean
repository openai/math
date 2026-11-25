import OAI.ThreeFlat.RAM.HistoryMotifTariffRefreshEntry
import OAI.ThreeFlat.Diagonal.RefreshHalfPrefix

namespace OAI
/-! # Refresh gather inputs and archived root fields -/

set_option quotPrecheck false

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HistoryGatherExecution RAM.HistoryGatherBody
open RAM.HistoryStageBody.Physical PhysicalStage NavigationDirectory CompressorPacking Native
open RefreshDemandRows RefreshStageNav RefreshTies RefreshParty
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u K endHeaders : ℕ} {cur ctr : Word (16*u^10)}
    (q : RefreshReceipt F K cur)
local notation "W" => 16*u^10
local notation "m" => 2^q.s
local notation "deg" => 1+q.h+q.pad
local notation "P" => CursorSpace.recordPointers q.entry
local notation "bound" => q.entry.next.heap
local notation "G" => numberedRefreshGraph q.input
local notation "nW" => numberedRefreshWidths q.input
local notation "w" => SlotImage.demandWidth nW
local notation "rW" => refreshNumericWidths q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch
local notation "H" => CompressorRefresh.graph G (DoublePorts.ofMatrix (Equiv.refl _) q.mult q.sym q.rowSum q.noLoop) q.hm q.pad
variable {final mem : Memory (16*u^10)}
    (saved : SavedFrame cur ctr endHeaders q.entry.next.header q.entry.next.heap q.out final)
    (limits : endHeaders ≤ q.cursor.heap ∧ q.entry.next.heap ≤ cur.val ∧ cur.val < ctr.val)
    (body : ∀ i,(q.cursor.header ≤ i ∧ i<q.entry.next.header ∨ endHeaders ≤ i)→
      i < q.entry.next.heap → mem i = final i)
    (y : (q.move.next q.term).Site)
local notation "z" => q.kernelSite y
local notation "ix" => (q.step.sites.ord y).val
local notation "site" => ((z).1.1,(z).2)
local notation "pt" => (z).1.2

include saved limits body in
omit [Fintype F] in
/-- Read the stage and the site number through the selected five-word kernel. -/
theorem selected_kernel {J : HistoryGatherBody.Layout} (kernel : (selected J mem).kernel.val=(P).kernel+ix*5) :
    (mem (selected J mem).kernel.val).val=q.cursor.header ∧ (wordAt mem (selected J mem).kernel 1).val=ix := by
  let read:=q.at_entry saved limits (fun j lo hi=>body j (.inr (limits.1.trans lo)) hi) .kernel
  have offset (f:Fin 5) : (Records.rowOrder deg .kernel (z,f)).val=ix*5+f.val:=by
    rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index];rfl
  have word (f:Fin 5) := read (z,f)
  have first:=word 0
  have second:=word 1
  rw [offset] at first second
  have oneRegion:=q.record_interval .kernel (Records.rowOrder deg .kernel (z,(1 : Fin 5)))
  rw [offset] at oneRegion
  have headFits:=q.issued.headerBelow
  have heapEnd:q.cursor.heap≤bound:=by change _≤(allocate K _ _).next.heap;rw [heap_step];omega
  have ixFit : ix<2^W:=by
    have near:(P).kernel+(ix*5+1)<bound:=oneRegion.2
    have a:=cur.isLt
    omega
  change mem ((P).kernel + ix*5) = (q.cursor.header : Word W) at first
  change mem ((P).kernel + (ix*5+1)) =
    (Records.siteId site pt : Word W) at second
  rw [q.kernelSite_index] at second
  constructor
  · rw [kernel,first,Fin.val_cast_of_lt (show q.cursor.header<2^W by have:=cur.isLt;omega)]
  · have fit:(P).kernel+ix*5+1<2^W:=by
      have near:(P).kernel+(ix*5+1)<bound:=oneRegion.2
      have:=cur.isLt
      omega
    have addr : ((selected J mem).kernel+(1:Word W)).val=(P).kernel+ix*5+1 := by
      calc
        _ = (selected J mem).kernel.val+1 := Fin.val_add_one_of_lt' (by rw [kernel]; exact fit)
        _ = _ := congrArg (fun n : ℕ => n+1) kernel
    change (mem ((selected J mem).kernel+(1:Word W)).val).val=ix
    rw [addr]
    rw [Nat.add_assoc,second,Fin.val_cast_of_lt ixFit]

include saved limits body in
omit [Fintype F] in
/-- The published width at the half computed by the native port decoder. -/
theorem selected_half_word (j:Fin (2*deg)) :
    mem ((P).halves+((ix*(2*deg)+j.val)*4+2))=(rW (ShrinkStage.Halves.sourceHalf H z j):Word W) := by
  let read:=q.at_entry saved limits (fun i lo hi=>body i (.inr (limits.1.trans lo)) hi) .halves
  have h:=read (z,Records.halfCol (j,2))
  have ordinal : (Records.rowOrder deg .halves (z,Records.halfCol (j,2))).val=ix*(8*deg)+j.val*4+2 := by
    rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index]
    change ix*(8*deg)+(Records.halfCol (j,(2:Fin 4))).val=_
    exact (congrArg (fun col => ix*(8*deg)+col) (Records.halfCol_val j (2:Fin 4))).trans
      (Nat.add_assoc _ _ _).symm
  rw [ordinal] at h
  have off:ix*(8*deg)+j.val*4+2=(ix*(2*deg)+j.val)*4+2:=by ring
  have field₂ (a b c d : ℕ) : (![a,b,c,d] : Fin 4→ℕ) 2=c := rfl
  simpa only [Records.Pointers.dst,Records.Table.value,Equiv.symm_apply_apply,field₂,off] using h

variable (J : HistoryGatherBody.Layout) (mode : J.mode = .refresh (2^q.s) q.h q.pad)
    (atParty : J.party.party = (q.kernelSite y).1.2.val) (portFit : 2^q.s < 2^(16*u^10))
    (kernel : (selected J mem).kernel.val =
      (CursorSpace.recordPointers q.entry).kernel + (q.step.sites.ord y).val*5)
    (rowPtr : (selected J mem).incident.val =
      (CursorSpace.recordPointers q.entry).motif + (q.step.sites.ord y).val*6)
    (arrays : OldArrayBounds endHeaders q.cursor q.input)
    (tileFit : q.tile.last+1 ≤ 2^(16*u^10))
    (histFit : (CursorSpace.recordPointers q.entry).counts+(q.chosenIndex y).val*K < 2^(16*u^10))
local notation "choice" => q.tile.winner (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input) (q.chosenBlock y)
local notation "issuedRecord" => issuedParty q.tile q.hh q.rowSum q.sym q.conn choice pt
variable {ar page : ℕ} (lib : ReadPage J mem (issuedParty q.tile q.hh q.rowSum q.sym q.conn
    (q.tile.winner (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input)
      (q.chosenBlock y)) (q.kernelSite y).1.2) ar page) (active : partyActive J mem)

include saved limits body mode atParty portFit kernel rowPtr arrays tileFit histFit lib active in
/-- A live old width comes from the real archived graph, in the dense port
ordering of the finite catalogue. The result uses the unnumbered selected tile. -/
theorem selected_demand_width (room : 4*m≤J.demandCap) (j : Fin (4*m))
    (banks : 3*m<2^W) (lanes : 2^q.rem<2^W)
    (widthFit : q.input.maxWidth<2^W) :
    (physicalWidth J mem false j.val).val=
      (profile (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input) (q.chosenBlock y))
        ((denseOrder pt j).val.1) := by
  let rr:=refreshWidthRegisters J mem false j.val
  have head: (rr 0).val=q.cursor.header := (q.selected_kernel saved limits body y kernel).1
  have opened:=q.source_at_entry saved limits arrays.graphLow arrays.widthLow body rr head
  have e:=q.elected_at_entry saved limits (fun i lo hi=>body i (.inr (limits.1.trans lo)) hi) y tileFit histFit 0
  have key : (mem (selected J mem).incident.val).val=blockId site := by
    rw [rowPtr]
    change (mem ((P).motif+ix*6)).val=(q.chosenIndex y).val at e
    exact e.trans (q.chosenIndex_val y)
  have pval:(J.party.party:Word W).val=(pt).val:=by rw [atParty,Fin.val_cast_of_lt ((pt).isLt.trans portFit)]
  obtain ⟨⟨dir,side,digit⟩,edge⟩:=(denseEnds pt).surjective (denseOrder pt j)
  have index : j.val=((if dir then 2 else 0)+(if side then 1 else 0))*m+digit.val:=by
    simpa only [edge,Equiv.symm_apply_apply] using dense_index pt digit dir side
  have pg:=lib.demand room j active
  have code:(portCode J mem false j.val).val=((if dir then 2 else 0)+(if side then 1 else 0))*m+digit.val :=
    (show (portCode J mem false j.val).val=j.val from pg.2).trans index
  have actual:=HistoryGatherBody.refresh_demand_width J mem mode j.val pg.1 site opened key pt digit dir side pval code banks lanes
  rw [edge] at actual
  have chart:numBlock q.input (q.chosenBlock y)=site:=by simp [numBlock,chosenBlock]
  have same:=congrFun (numProfile q.input (q.chosenBlock y)) ((denseOrder pt j).val.1)
  rw [chart] at same
  have cap:=q.input.width_le_maxWidth ((StageAddress.refreshEdge (splitWord q.s q.rem) (tagOrdinal q.s).symm).symm
    (addr (arrival (refreshBinaryGraph q.input) (tagOrdinal q.s).symm) (q.chosenBlock y) ((denseOrder pt j).val.1)))
  change profile G (tagOrdinal q.s).symm w site ((denseOrder pt j).val.1) = _ at same
  rw [actual]
  exact (Fin.val_cast_of_lt (same.le.trans_lt (cap.trans_lt widthFit))).trans same


include saved limits body in
omit [Fintype F] in
/-- The stage directory retained the absolute base of its actual fresh half table. -/
theorem half_table_at {J : HistoryGatherBody.Layout} (kernel : (selected J mem).kernel.val=(P).kernel+ix*5) :
    (mem ((mem (selected J mem).kernel.val).val+40)).val=(P).halves := by
  rw [(q.selected_kernel saved limits body y kernel).1]
  have hi:=q.issued.headerBelow
  have heap:q.cursor.heap≤bound:=by change _≤(allocate K _ _).next.heap;rw [heap_step];omega
  have r : q.cursor.header+40<q.entry.next.header := by change q.cursor.header+40<q.cursor.header+64;omega
  rw [body _ (.inl ⟨Nat.le_add_right ..,r⟩) (by omega),saved _ (by omega) (by omega) (.inl r) (by omega)]
  exact q.issued.archivedHeader 40 (by decide)

local notation "bh" => refreshBinaryBranchOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch
local notation "sp" => q.tile.widths G (tagOrdinal q.s).symm w (numBranches q.tile q.input bh)
local notation "actualSp" => q.tile.widths (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input) bh

include saved limits body in
omit [Fintype F] in
/-- Width of either direction of the elected sparse port. Its half is fetched
from this site's actual four-word record after the stage cursor has moved on. -/
theorem selected_supply_row {J : HistoryGatherBody.Layout} (kernel : (selected J mem).kernel.val=(P).kernel+ix*5)
    (a : (ports q.mult).Port pt) (wordFit : actualSp (q.chosenBlock y) a.val.1<2^W) :
    let s:=(numbering q.mult q.rowSum (if a.val.2 then DoublePorts.reverseArc q.mult q.sym a.val.1 else a.val.1)).2
    let half:=1+(if a.val.2 then deg else 0)+s.val
    let siteNumber:=(wordAt mem (selected J mem).kernel 1).val
    let table:=(mem ((mem (selected J mem).kernel.val).val+40)).val
    (mem (table+((siteNumber*(2*deg)+half)*4+2))).val=actualSp (q.chosenBlock y) a.val.1 := by
  dsimp only
  rw [q.half_table_at saved limits body y kernel,(q.selected_kernel saved limits body y kernel).2]
  let s:=(numbering q.mult q.rowSum (if a.val.2 then DoublePorts.reverseArc q.mult q.sym a.val.1 else a.val.1)).2
  let j:Fin (2*deg):=⟨1+(if a.val.2 then deg else 0)+s.val,by have:=s.isLt;split_ifs <;> omega⟩
  have got:=q.selected_half_word saved limits body y j
  have size : rW (ShrinkStage.Halves.sourceHalf H z j)=sp site a.val.1 :=
    sparse_half_width G q.mult q.sym q.rowSum q.noLoop q.hm q.pad w sp site pt a j rfl
  have shape:(numBlockEquiv q.input).symm site=q.chosenBlock y:=rfl
  have real:sp site a.val.1=actualSp (q.chosenBlock y) a.val.1:=by
    simpa only [shape] using numBranches_width q.tile q.input bh site a.val.1
  rw [size,real] at got
  exact (congrArg Fin.val got).trans (Fin.val_cast_of_lt wordFit)

include saved limits body mode kernel arrays lib active in
/-- Native width of the issued S38 supply slot from both tables and its selected histogram. -/
theorem selected_supply_width (room : 2*q.h≤J.supplyCap) (j : Fin (2*q.h)) (degree : q.h<2^W)
    (fits : actualSp (q.chosenBlock y) ((sparseOrder q.mult q.sym q.rowSum pt j).val.1)<2^W) :
    (physicalWidth J mem true j.val).val=actualSp (q.chosenBlock y) ((sparseOrder q.mult q.sym q.rowSum pt j).val.1) := by
  let a:=sparseOrder q.mult q.sym q.rowSum pt j
  let k:=(numbering q.mult q.rowSum (if a.val.2 then DoublePorts.reverseArc q.mult q.sym a.val.1 else a.val.1)).2
  let rr:=refreshWidthRegisters J mem true j.val
  have head:(rr 0).val=q.cursor.header := (q.selected_kernel saved limits body y kernel).1
  have opened:=q.source_at_entry saved limits arrays.graphLow arrays.widthLow body rr head
  have pg:=lib.supply room j active
  have code:(portCode J mem true j.val).val=(if a.val.2 then q.h else 0)+k.val := by
    have ca : (portCode J mem true j.val).val=j.val:=pg.2
    rw [ca]
    simpa only [a,Equiv.symm_apply_apply] using sparse_index q.mult q.sym q.rowSum pt a
  let N:=Fintype.card q.input.Base*m*2^q.rem
  have ixBound:ix<N:=by
    have h:=(Records.siteOrder z).isLt
    rwa [Records.siteOrder_val,q.kernelSite_index] at h
  have count:(wordAt mem (selected J mem).kernel 1).val<N:=by rw [(q.selected_kernel saved limits body y kernel).2];exact ixBound
  have cap:(P).halves+N*(2*deg)*4≤2^W:=by
    have last: (P).halves+Records.length (Fintype.card q.input.Base) m q.rem deg .halves ≤q.entry.words 42 :=
      (CursorSpace.retained_addresses (c:=q.cursor) (K:=K) (v:=Fintype.card q.input.Base) (a:=q.s) (t:=q.rem)
        (h:=q.h) (pad:=q.pad)).2.2.2.2 .halves
    have next:q.entry.words 42≤bound := by
      obtain ⟨pinsEnd,ownersEnd,_⟩:=RefreshNodeOwners.owner_spans (c:=q.cursor) (v:=Fintype.card q.input.Base)
        (a:=q.s) (t:=q.rem) (h:=q.h) (pad:=q.pad) (K:=K)
      calc
        q.entry.words 42 ≤ q.entry.words 42+N := Nat.le_add_right _ _
        _ = q.entry.words 44 := pinsEnd
        _ ≤ q.entry.words 44+N := Nat.le_add_right _ _
        _ = q.entry.next.heap := ownersEnd
    have len:Records.length (Fintype.card q.input.Base) m q.rem deg .halves =N*(2*deg)*4 := by
      change N*(8*deg)=_;ring
    rw [len] at last
    exact last.trans (next.trans (limits.2.1.trans cur.isLt.le))
  have run:=HistoryGatherBody.refresh_supply_width J mem mode j.val opened N count k a.val.2 code
    (actualSp (q.chosenBlock y) a.val.1) (q.selected_supply_row saved limits body y kernel a fits)
    (by rw [q.half_table_at saved limits body y kernel];exact cap) degree pg.1
  exact (congrArg Fin.val run).trans (Fin.val_cast_of_lt fits)

include saved limits body atParty rowPtr tileFit histFit in
/-- Recover the selected physical port catalogue for this actual journal entry. -/
theorem selected_page (B : Block F) {height base : ℕ} (lib : Mounted B height W base mem)
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (kindBase : J.party.kinds=(refreshFamily B base height).kinds)
    (portBase : J.catalogue=(refreshFamily B base height).ports)
    (d : J.demandCap=(refreshGrid B).demand) (s : J.supplyCap=(refreshGrid B).supply)
    (digits : J.digitCap=(refreshGrid B).digits) (parties : J.party.parties=m)
    (kindRoom : (refreshFamily B base height).kinds+7*((choice).val*m+(pt).val)+7≤2^W)
    (pgRoom : (refreshFamily B base height).ports+(refreshGrid B).stride*((choice).val*m+(pt).val)+(refreshGrid B).stride≤2^W)
    (kindFit : ∀ i:Fin 7,((issuedRecord).kind (arity B)).words i<2^W)
    (portWord : ∀ i:Fin (refreshGrid B).stride,(issuedRecord).port.at (refreshGrid B).demand (refreshGrid B).supply i.val<2^W) :
    ReadPage J mem issuedRecord (arity B) ((refreshFamily B base height).ports+(refreshGrid B).stride*((choice).val*m+(pt).val)) := by
  let elected:=q.elected_at_entry saved limits (fun i lo hi=>body i (.inr (limits.1.trans lo)) hi) y tileFit histFit
  let rom:=issued_party_rom B lib q.tile supported q.hh q.rowSum q.sym q.conn choice pt
  have span:=q.record_interval .motif (Records.rowOrder deg .motif (z,(2:Fin 6)))
  rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index] at span
  have rowFit:(P).motif+ix*6+2<2^W:=by have last:(P).motif+(ix*6+2)<bound:=span.2;have:=cur.isLt;omega
  have shape : wordAt mem (selected J mem).incident 2=((choice).val:Word W) := by
    apply Fin.ext
    have addr : ((selected J mem).incident+(2:Word W)).val=(P).motif+ix*6+2:=by
      have two : (2 : Word W).val = 2 := by
        change 2 % (2^W) = 2
        exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, two, rowPtr, Nat.mod_eq_of_lt rowFit]
    change (mem ((selected J mem).incident+(2:Word W)).val).val=_
    rw [addr,Fin.val_cast_of_lt ((choice).isLt.trans_le tileFit)]
    exact elected 2
  let pre:=List.ofFn (shrinkGrid B)
  have pages:=Mounted.selected_pages (B:=B) («G»:=refreshGrid B) (pre:=pre) («m»:=mem) J choice pt
    kindBase portBase d s digits parties atParty shape
  have stride : HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap=(refreshGrid B).stride := by rw [d,s,digits];rfl
  refine ⟨pages.2,by simpa only [stride] using pgRoom,?_,?_⟩
  · intro i
    have kindPage : (selected J mem).kindPage =
        (((refreshFamily B base height).kinds + 7*((choice).val*m+(pt).val) : ℕ) : Word W) := pages.1
    have kindBound :
        (refreshFamily B base height).kinds + 7*((choice).val*m+(pt).val) + i.val < 2^W :=
      (Nat.add_lt_add_left i.isLt _).trans_le kindRoom
    unfold wordAt
    rw [kindPage,←Nat.cast_add,Fin.val_cast_of_lt kindBound]
    exact (congrArg Fin.val (rom.2.2.1 i)).trans (Fin.val_cast_of_lt (kindFit i))
  · intro j h
    rw [stride] at h
    rw [d,s]
    exact (congrArg Fin.val (rom.2.2.2 ⟨j,h⟩)).trans (Fin.val_cast_of_lt (portWord ⟨j,h⟩))

omit [Fintype F] in
/-- Numbering the base never changes any of the four numerical coordinates,
including the prefix of earlier lanes in an incoming external bundle. -/
theorem number_demand_location (vtx : q.input.Base×BitWord q.rem) (port : Fin m)
    (j : (RefreshMotif.denseGraph m).Port port) (bit : ℕ) :
    demandLocation (h:=q.h) (pad:=q.pad) (arrival G (tagOrdinal q.s).symm) w (numBlock q.input vtx) port j bit=
    demandLocation (h:=q.h) (pad:=q.pad) (arrival (refreshBinaryGraph q.input) (tagOrdinal q.s).symm)
      (refreshBinaryInput q.input) vtx port j bit := by
  obtain ⟨⟨⟨dir,i,k⟩,side⟩,e⟩:=j
  let locate {Z : Type} (width : Address Z m → ℕ) (a : Address Z m) : RefreshParty.Location ℕ :=
    ⟨if bit < width a then (if side then 2 else 1) else 0, 0,
      if side then (if dir then 1+q.h+q.pad else 0) else k.val+(if dir then m else 0),
      if side then (∑ t : Fin a.2.1.val, width (a.1,Fin.castLE a.2.1.isLt.le t,a.2.2))+bit else bit⟩
  change locate w (addr (arrival G (tagOrdinal q.s).symm) (numBlock q.input vtx) (dir,i,k)) =
    locate (refreshBinaryInput q.input) (addr (arrival (refreshBinaryGraph q.input)
      (tagOrdinal q.s).symm) vtx (dir,i,k))
  rw [numArrival]
  have lane (v : q.input.Base × BitWord q.rem) (first second : Fin (2^q.s)) :
      w (numBlock q.input v,first,second)=refreshBinaryInput q.input (v,first,second) :=
    numWidth q.input (v,first,second)
  simp only [locate, numAddress, lane]

include saved limits body mode atParty portFit kernel rowPtr arrays tileFit histFit lib active in
/-- Geometry for a live demand port, landing in either the sole child's pin or
the fresh external half. All old graph rows and scan widths come from q. -/
theorem selected_demand_geometry (room : 4*m≤J.demandCap) (j : Fin (4*m))
    (bit : ℕ) (banks : 3*m<2^W) (lanes : 2^q.rem<2^W) (small : 4≤2^W)
    (aperture : srcBase J false j.val+bit<2^W)
    {hidden pins:ℕ} (target : BitSource hidden pins)
    (fits : HistoryGeometryPointer.ReadFits mem (sourceRegisters J mem false j.val (bit:Word W))
      (fun f=>component (demandLocation (h:=q.h) (pad:=q.pad)
        (arrival (refreshBinaryGraph q.input) (tagOrdinal q.s).symm) (refreshBinaryInput q.input)
        (q.chosenBlock y) pt (denseOrder pt j) bit) f.val))
    (typed : HistoryScopeAddress.Read (HistoryGeometryPointer.layoutOf (sourceRegisters J mem false j.val (bit:Word W)))
      (fun i=>(mem i).val) (fun f=>component (demandLocation (h:=q.h) (pad:=q.pad)
        (arrival (refreshBinaryGraph q.input) (tagOrdinal q.s).symm) (refreshBinaryInput q.input)
        (q.chosenBlock y) pt (denseOrder pt j) bit) f.val) target) :
    (geometryTerm W J false).eval (fun _=>0) mem (sourceRegisters J mem false j.val (bit:Word W))=
      (BitLayout.sourceAddress target:Word W) := by
  let rr:=refreshWidthRegisters J mem false j.val
  have openSrc:=q.source_at_entry saved limits arrays.graphLow arrays.widthLow body rr
    (q.selected_kernel saved limits body y kernel).1
  obtain ⟨⟨dir,side,digit⟩,edge⟩:=(denseEnds pt).surjective (denseOrder pt j)
  have pageRead:=lib.demand room j active
  have code:(portCode J mem false j.val).val=((if dir then 2 else 0)+(if side then 1 else 0))*m+digit.val :=
    (show (portCode J mem false j.val).val=j.val from pageRead.2).trans (by
      simpa only [edge,Equiv.symm_apply_apply] using dense_index pt digit dir side)
  have chosen:=q.elected_at_entry saved limits (fun i lo hi=>body i (.inr (limits.1.trans lo)) hi) y tileFit histFit 0
  have baseRow:(mem (selected J mem).incident.val).val=blockId site := by rw [rowPtr];exact chosen.trans (q.chosenIndex_val y)
  have numbered : numBlock q.input (q.chosenBlock y)=site:=by simp [numBlock,chosenBlock]
  have loc : denseLocation G nW q.h q.pad site pt digit dir side bit=(fun f:Fin 4=>component
      (demandLocation (h:=q.h) (pad:=q.pad) (arrival (refreshBinaryGraph q.input) (tagOrdinal q.s).symm)
        (refreshBinaryInput q.input) (q.chosenBlock y) pt (denseOrder pt j) bit) f.val) := by
    funext f
    unfold denseLocation
    rw [←numbered,edge,q.number_demand_location]
  have answers := source_from_geometry J mem false j.val bit (BitLayout.sourceAddress target:Word W) aperture
  refine (answers ?_).1
  intro ptr ok
  apply HistoryGatherBody.refresh_demand_source J mem mode j.val bit ptr site pt digit dir side ok openSrc baseRow
    (by rw [atParty,Fin.val_cast_of_lt ((pt).isLt.trans portFit)]) code banks lanes small target
  · rw [loc];exact fits
  · rw [loc];exact typed

open HistoryGeometryPointer HistoryScopeAddress
local notation "actualG" => refreshBinaryGraph q.input
local notation "actualW" => refreshBinaryInput q.input
local notation "actualZ" => q.chosenBlock y
local notation "π" => arrival actualG (tagOrdinal q.s).symm
local notation "δ" => externalSite actualG
local notation "S" => (fun _ : q.input.Base×BitWord q.rem=>ports q.mult)
local notation "bw" => termWidth q.mult actualW actualSp
variable {pins hidden : ℕ}
  (old : (a : (oldPortGraph (arrival (refreshBinaryGraph q.input) (tagOrdinal q.s).symm)).Port
      (q.chosenBlock y,(q.kernelSite y).1.2)) → Fin (refreshBinaryInput q.input a.val.1) → Fin pins)
  (new : (a : (actualPortGraph (outputGraph (refreshBinaryGraph q.input) q.mult q.sym q.rowSum
      q.noLoop q.hm q.pad)).Port (q.chosenBlock y,(q.kernelSite y).1.2)) →
    Fin (freshWidth q.mult q.rowSum
      (termWidth q.mult (refreshBinaryInput q.input)
        (q.tile.widths (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input)
          (refreshBinaryBranchOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch)))
      q.pad a.val.1) → Fin pins)
local notation "fresh" => actualBit actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad bw new
local notation "dest" => external_site actualG (tagOrdinal q.s).symm
local notation "memory" => (fun a=>(mem a).val)

include saved limits body mode atParty portFit kernel rowPtr arrays tileFit histFit lib active in
/-- Emit the selected site's true demanded input bit through the archived
child or fresh singleton bundle. The only variable input cells are the real
address table and the two port prefix sums. -/
theorem selected_demand_pin (room : 4*m≤J.demandCap) (slot : Fin (4*m))
    (bit : Fin (actualW (addr π actualZ (denseOrder pt slot).val.1)))
    (banks : 3*m<2^W) (lanes : 2^q.rem<2^W) (small : 4≤2^W)
    (aperture : srcBase J false slot.val+bit.val<2^W)
    (O : RefreshOld (layoutOf (sourceRegisters J mem false slot.val (bit.val:Word W))) memory)
    (N : RefreshNew (layoutOf (sourceRegisters J mem false slot.val (bit.val:Word W))) memory)
    (oldPrefix : ∀(p : (oldPortGraph π).Port (actualZ,pt)) (b : Fin (actualW p.val.1)),
      O.pin (oldHalf π actualZ pt p) b.val=(old p b).val)
    (newPrefix : ∀(p : (rawGraph δ S).Port (actualZ,pt)) (b : Fin (bw p.val.1)),
      N.pin (freshHalf (pad:=q.pad) δ q.mult q.sym q.rowSum actualZ pt p) b.val=(fresh p b).val) :
    let source:=demandPin π δ dest S actualW actualSp actualZ pt old fresh (denseOrder pt slot) bit
    let loc:=demandLocation (h:=q.h) (pad:=q.pad) π actualW actualZ pt (denseOrder pt slot) bit.val
    let T:=layoutOf (sourceRegisters J mem false slot.val (bit.val:Word W))
    (loc.scope=1→ T.childIDs<2^W ∧ T.nodes+(8*O.child+6)<2^W ∧ O.header+1<2^W ∧
       O.table+(4*loc.half+3)<2^W ∧ T.childStarts<2^W) →
    (loc.scope=2→ T.newHalves+1<2^W ∧ N.table+(4*loc.half+3)<2^W) →
    (geometryTerm W J false).eval (fun _=>0) mem (sourceRegisters J mem false slot.val (bit.val:Word W))=
      (BitLayout.sourceAddress (.pin source:BitSource hidden pins):Word W) := by
  intro source loc T oldRoom freshRoom
  let fields:=fun f:Fin 4=>component loc f.val
  have tag:loc.scope=1 ∨ loc.scope=2 := by
    have scopes (i len : ℕ) (sideFlag : Bool) (fitsBit : i < len) :
        (if i < len then (if sideFlag then 2 else 1) else 0) = 1 ∨
        (if i < len then (if sideFlag then 2 else 1) else 0) = 2 := by
      cases sideFlag <;> simp [fitsBit]
    exact scopes bit.val (actualW (addr π actualZ (denseOrder pt slot).val.1))
      (denseOrder pt slot).val.2 bit.isLt
  have tag0:fields 0=loc.scope:=rfl
  have c1:fields 1=0:=rfl
  have c2:fields 2=loc.half:=rfl
  have fits:ReadFits mem (sourceRegisters J mem false slot.val (bit.val:Word W)) fields := by
    apply readFits_of_addresses _ _ _ (by omega) (by omega)
    · intro branch
      simpa only [c1,c2,Nat.add_zero,O.idAt,O.headerAt,O.tableAt] using oldRoom (tag0 ▸ branch)
    · intro branch
      simpa only [c2,N.tableAt] using freshRoom (tag0 ▸ branch)
    · omega
  have typed:=HistoryScopeAddress.Read.refreshDemand (hidden:=hidden) (pad:=q.pad) π δ dest q.mult q.sym q.rowSum
    actualW actualSp actualZ pt old fresh T memory O N (denseOrder pt slot) bit oldPrefix newPrefix
  exact q.selected_demand_geometry saved limits body y J mode atParty portFit kernel rowPtr arrays tileFit histFit
    lib active room slot bit.val banks lanes small aperture (.pin source) fits typed

include saved limits body mode kernel arrays lib active in
/-- Emit the sparse output pin of the same original histogram tile. The only
dynamic source prefix is read from the published successor half word. -/
theorem selected_supply_pin (room : 2*q.h≤J.supplyCap) (slot : Fin (2*q.h))
    (b : Fin (actualSp actualZ ((sparseOrder q.mult q.sym q.rowSum pt slot).val.1)))
    (widthFit : actualSp actualZ ((sparseOrder q.mult q.sym q.rowSum pt slot).val.1)<2^W)
    (small : 4≤2^W) (degree : q.h<2^W) (aperture : srcBase J true slot.val+b.val<2^W)
    (N : RefreshNew (layoutOf (sourceRegisters J mem true slot.val (b.val:Word W))) memory)
    (newPrefix : ∀ (p : (rawGraph δ S).Port (actualZ,pt)) (i : Fin (bw p.val.1)),
      N.pin (freshHalf (pad:=q.pad) δ q.mult q.sym q.rowSum actualZ pt p) i.val=(fresh p i).val)
    (tableCap : (P).halves+(Fintype.card q.input.Base*m*2^q.rem)*(2*deg)*4≤2^W) :
    let a:=sparseOrder q.mult q.sym q.rowSum pt slot
    let src:=sparsePin δ S actualW actualSp actualZ pt fresh a b
    let k:=(numbering q.mult q.rowSum (if a.val.2 then DoublePorts.reverseArc q.mult q.sym a.val.1 else a.val.1)).2
    (layoutOf (sourceRegisters J mem true slot.val (b.val:Word W))).newHalves+1<2^W →
    N.table+(4*(1+(if a.val.2 then deg else 0)+k.val)+3)<2^W →
    (geometryTerm W J true).eval (fun _=>0) mem (sourceRegisters J mem true slot.val (b.val:Word W))=
      (BitLayout.sourceAddress (.pin src:BitSource hidden pins):Word W) := by
  intro a src k headFit halfFit
  let regs:=sourceRegisters J mem true slot.val (b.val:Word W)
  let locs:=sparseLocationWords q.h q.pad k a.val.2 b.val (actualSp actualZ a.val.1)
  have typed : HistoryScopeAddress.Read (layoutOf regs) memory locs (.pin src:BitSource hidden pins) :=
    HistoryScopeAddress.Read.refreshSupply (pad:=q.pad) δ q.mult q.sym q.rowSum actualW
      actualSp actualZ pt fresh _ memory N a b newPrefix
  have tag : locs 0 = 2 :=
    ite_eq_left (show b.val < actualSp actualZ a.val.1 from b.isLt)
  have fits : ReadFits mem regs locs := by
    apply readFits_of_addresses _ _ _ (by omega) (by omega)
    · omega
    · intro _
      exact ⟨headFit, (congrArg (fun t : ℕ => t + (4 * locs 2 + 3)) N.tableAt).le.trans_lt halfFit⟩
    · omega
  have pg:=lib.supply room slot active
  have ca:(portCode J mem true slot.val).val=slot.val:=pg.2
  have code:(portCode J mem true slot.val).val=(if a.val.2 then q.h else 0)+k.val := by
    rw [ca];simpa only [a,Equiv.symm_apply_apply] using sparse_index q.mult q.sym q.rowSum pt a
  have opened:=q.source_at_entry saved limits arrays.graphLow arrays.widthLow body (refreshWidthRegisters J mem true slot.val)
    (q.selected_kernel saved limits body y kernel).1
  let sites:=Fintype.card q.input.Base*m*2^q.rem
  have siteFit:(wordAt mem (selected J mem).kernel 1).val<sites:=by
    rw [(q.selected_kernel saved limits body y kernel).2]
    have h:=(Records.siteOrder z).isLt
    rwa [Records.siteOrder_val,q.kernelSite_index] at h
  refine (source_from_geometry J mem true slot.val b.val _ aperture ?_).1
  intro ptr key
  exact HistoryGatherBody.refresh_supply_source J mem mode slot.val b.val ptr opened sites siteFit k a.val.2
    code (actualSp actualZ a.val.1) (q.selected_supply_row saved limits body y kernel a widthFit)
    (by rw [q.half_table_at saved limits body y kernel];exact tableCap) degree key small _ fits typed

omit [Fintype F] in
/-- Numeric range of the selected output comes from the exact sparse word
published in the admitted run, for either orientation of the half. -/
theorem selected_width_fits (a : Expander.Arc q.mult) : actualSp actualZ a<2^W := by
  let e:=numbering q.mult q.rowSum a
  have actual:=q.issued.sparse actualZ e.1 e.2
  have h:(numbering q.mult q.rowSum).symm (e.1,e.2)=a:=(numbering q.mult q.rowSum).symm_apply_apply a
  rw [h] at actual
  rw [←actual]
  exact Fin.isLt _

omit [Fintype F] in
theorem old_width_fits : q.input.maxWidth<2^W := by
  have each (e) : q.input.width e<2^W:=by
    rw [←q.stored.widthWord e]
    exact Fin.isLt _
  exact Nat.lt_of_le_of_lt (Finset.sup_le (fun e _=>Nat.le_pred_of_lt (each e)))
    (Nat.pred_lt (Nat.two_pow_pos _).ne')

/-- Memory cells outside the S17 slice read by one live refresh arm. -/
structure PortWindow (J : HistoryGatherBody.Layout) (input : Memory W) (page demandEnd : ℕ) : Prop where
  mask : MaskRoom J input J.temp (portsEnd J)
  incident : let p:=((selected J input).kernel+4).val
    p<J.temp ∨ portsEnd J≤p
  kind : let p:=((selected J input).incident+2).val
    p<J.temp ∨ portsEnd J≤p
  kindRows : ∀ i:Fin 7,let p:=((selected J input).kindPage+(i.val:Word W)).val
    p<J.temp ∨ portsEnd J≤p
  pageCells : ∀ i,i<demandEnd→ page+i<J.temp ∨ portsEnd J≤page+i
  stageCells : ∀ i,(q.cursor.header ≤ i ∧ i<q.entry.next.header ∨ endHeaders ≤ i)→i<bound→i<J.temp ∨ portsEnd J ≤ i

/-- Re-open an active refresh site after writing some or all of its port buffers. -/
theorem PortWindow.after_port {J : HistoryGatherBody.Layout} {input scratch : Memory W}
    {p : Party F} {ar page:ℕ}
    (window : q.PortWindow (endHeaders:=endHeaders) J input page (HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap))
    (rows : ReadPage J input p ar page) (active : partyActive J input)
    (keep : DescriptorScan.agreesOutside J.temp (portsEnd J) scratch input) :
    (selected J scratch).kernel=(selected J input).kernel ∧
    (selected J scratch).incident=(selected J input).incident ∧ ReadPage J scratch p ar page ∧
    partyActive J scratch ∧ ∀i,(q.cursor.header ≤ i ∧ i<q.entry.next.header ∨ endHeaders ≤ i)→i<bound→scratch i=input i := by
  have cursor:=keep _ window.mask.cursor
  have node:=keep _ window.mask.node
  have ptr:=selected_rows_same J cursor node (keep _ window.incident) (keep _ window.kind)
  have ker:(selected J scratch).kernel=(selected J input).kernel:=by
    change scratch (nodeWord J scratch+5).val=input (nodeWord J input+5).val
    rw [node_stable J cursor,node]
  refine ⟨ker,ptr.1,⟨ptr.2.2.trans rows.base,rows.extent,?_,?_⟩,(window.mask.active keep).2 active,?_⟩
  · intro i
    unfold wordAt
    rw [ptr.2.1,keep _ (window.kindRows i)]
    exact rows.kinds i
  · intro i hi
    exact (congrArg Fin.val (keep _ (window.pageCells i hi))).trans (rows.ports i hi)
  · exact fun i hi top=>keep i (window.stageCells i hi top)

open private header_congr from OAI.ThreeFlat.RAM.HistoryGatherBody

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
include saved limits body in
/-- The selected refresh row keeps exactly the same S17 header after a partial
header write. Both live width branches re-read the issued stage and graph, and
every padding width is zero by the arities on the resident catalogue page. -/
theorem header_window (J : HistoryGatherBody.Layout) (mode : J.mode=.refresh m q.h q.pad)
    (atParty : J.party.party=(pt).val) (portFit : m<2^W)
    (kernel : (selected J mem).kernel.val=(P).kernel+ix*5)
    (rowPtr : (selected J mem).incident.val=(P).motif+ix*6)
    (arrays : OldArrayBounds endHeaders q.cursor q.input)
    (tileFit : q.tile.last+1≤2^W) (histFit : (P).counts+(q.chosenIndex y).val*K<2^W)
    {ar page:ℕ} (reg : ReadPage J mem issuedRecord ar page) (enabled : partyActive J mem)
    (window : q.PortWindow (endHeaders:=endHeaders) J mem page (HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap))
    (nd : 4*m≤J.demandCap) (ns : 2*q.h≤J.supplyCap)
    (banks : 3*m<2^W) (lanes : 2^q.rem<2^W) (degree : q.h<2^W)
    (headRoom : J.temp+(@HistoryGatherBody.fields (16*u^10) J).length≤J.temp+J.party.V)
    (pairInfo : ((selected J mem).privatePage 1+1).val<J.temp) :
    HeaderFootprint J mem J.temp (J.temp+(@HistoryGatherBody.fields (16*u^10) J).length) := by
  constructor
  intro scratch frame
  have pageEnd : J.temp+J.party.V≤portsEnd J := by
    unfold portsEnd
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  have keep : DescriptorScan.agreesOutside J.temp (portsEnd J) scratch mem := by
    intro a ha
    apply frame
    exact ha.imp id (fun h=>headRoom.trans (pageEnd.trans h))
  obtain ⟨ker,inc,reg',active,same⟩:=PortWindow.after_port q window reg enabled keep
  have body' : ∀ i,(q.cursor.header ≤ i ∧ i<q.entry.next.header ∨ endHeaders ≤ i)→i<bound→scratch i=final i :=
    fun i inside hi=>(same i inside hi).trans (body i inside hi)
  have capFits (side:Bool) (i:ℕ) (hi:i<cap J side) : i<2^W := by
    have ext:=reg.extent
    dsimp only [HistoryPortCatalogue.stride] at ext
    cases side <;> dsimp [cap] at hi <;> omega
  have countAt (side:Bool) :
      (wordAt scratch (selected J scratch).portPage side.toNat).val=
        (wordAt mem (selected J mem).portPage side.toNat).val := by
    have n : side.toNat<HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap := by
      cases side <;> simp [HistoryPortCatalogue.stride]; omega
    exact (reg'.word side.toNat n).trans (reg.word side.toNat n).symm
  have port (side:Bool) (i:ℕ) (hi:i<cap J side) :
      portActive J scratch side i ↔ portActive J mem side i := by
    rw [portActive_iff J scratch side i (capFits side i hi),portActive_iff J mem side i (capFits side i hi),countAt]
    simp only [active,enabled,true_and]
  have pad (side:Bool) (i:ℕ) (hi:i<cap J side) (off:(if side then 2*q.h else 4*m) ≤ i) :
      ¬portActive J mem side i := by
    intro used
    have h:=((portActive_iff J mem side i (capFits side i hi)).1 used).2
    have n : side.toNat<HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap := by
      cases side <;> simp [HistoryPortCatalogue.stride]; omega
    rw [reg.word side.toNat n] at h
    cases side <;> simp [issuedParty,HistoryPortCatalogue.Page.at,Party.ofTile] at h off <;> omega
  have wide (side:Bool) (i:ℕ) (hi:i<cap J side) :
      physicalWidth J scratch side i=physicalWidth J mem side i := by
    by_cases chosen : i<(if side then 2*q.h else 4*m)
    · cases side
      · let j : Fin (4*m):=⟨i,chosen⟩
        exact Fin.ext ((q.selected_demand_width saved limits body' y J mode atParty portFit
          ((congrArg Fin.val ker).trans kernel) ((congrArg Fin.val inc).trans rowPtr) arrays tileFit histFit
          reg' active nd j banks lanes q.old_width_fits).trans (q.selected_demand_width saved limits body y J mode
          atParty portFit kernel rowPtr arrays tileFit histFit reg enabled nd j banks lanes q.old_width_fits).symm)
      · let j : Fin (2*q.h):=⟨i,chosen⟩
        have fits:=q.selected_width_fits y ((sparseOrder q.mult q.sym q.rowSum pt j).val.1)
        exact Fin.ext ((q.selected_supply_width saved limits body' y J mode ((congrArg Fin.val ker).trans kernel)
          arrays reg' active ns j degree fits).trans
          (q.selected_supply_width saved limits body y J mode kernel arrays reg enabled ns j degree fits).symm)
    · have empty:=pad side i hi (Nat.le_of_not_gt chosen)
      simp only [physicalWidth,ite_eq_right empty,ite_eq_right (fun yes=>empty ((port side i hi).1 yes))]
  have cursor:=keep _ window.mask.cursor
  have copies : wordAt scratch (selected J scratch).incident 3=wordAt mem (selected J mem).incident 3 := by
    have r:=q.record_interval .motif (Records.rowOrder (1+q.h+q.pad) .motif (z,(3 : Fin 6)))
    rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index] at r
    have low : q.cursor.heap≤(P).motif+(ix*6+3):=r.1
    have high : (P).motif+(ix*6+3)<bound:=r.2
    have fit : (P).motif+ix*6+3<2^W:=by have:=cur.isLt;omega
    unfold wordAt
    rw [inc,←Fin.cast_val_eq_self (selected J mem).incident,rowPtr,←Nat.cast_add,Fin.val_cast_of_lt fit]
    exact same _ (.inr (by omega)) (by omega)
  have bits : wordAt scratch (selected J scratch).kindPage 2=wordAt mem (selected J mem).kindPage 2 :=
    Fin.ext ((reg'.kinds 2).trans (reg.kinds 2).symm)
  have mapCount : partyMapCount J scratch=partyMapCount J mem := by
    simp only [partyMapCount,ite_eq_left active,ite_eq_left enabled,wordAt,privatePage_stable J cursor 1]
    exact frame _ (.inl pairInfo)
  unfold headerWords
  rw [privatePage_stable J cursor 2,mapCount]
  apply header_congr J _ _ wide
  · intro i hi
    simp only [payloadWidth,ite_eq_left active,ite_eq_left enabled,copies,bits,wide true i hi]
  · intro i hi
    unfold tileWidth
    rw [propext (port false i hi)]
    split
    · have n : HistoryPortCatalogue.demandBase+2*i+1<HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap := by
        simp only [HistoryPortCatalogue.demandBase,HistoryPortCatalogue.stride];omega
      exact Fin.ext ((reg'.word _ n).trans (reg.word _ n).symm)
    · rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
include saved limits body in
/-- Every actual refresh source scan fits its bank when the adjacent physical
states fit. A sparse supply width is an actual edge of the successor state. -/
theorem selected_port_fits (J : HistoryGatherBody.Layout) (mode : J.mode=.refresh m q.h q.pad)
    (atParty : J.party.party=(pt).val) (portFit : m<2^W)
    (kernel : (selected J mem).kernel.val=(P).kernel+ix*5)
    (rowPtr : (selected J mem).incident.val=(P).motif+ix*6)
    (arrays : OldArrayBounds endHeaders q.cursor q.input)
    (tileFit : q.tile.last+1≤2^W) (histFit : (P).counts+(q.chosenIndex y).val*K<2^W)
    {ar page:ℕ} (reg : ReadPage J mem issuedRecord ar page) (enabled : partyActive J mem)
    (nd : 4*m≤J.demandCap) (ns : 2*q.h≤J.supplyCap)
    (banks : 3*m<2^W) (lanes : 2^q.rem<2^W) (degree : q.h<2^W)
    (oldMax : q.input.maxWidth≤J.party.V)
    (newMax : ((refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn).next q.branch).maxWidth≤J.party.V) :
    ∀ side i,i<cap J side → (physicalWidth J mem side i).val≤J.party.V := by
  intro side i hi
  by_cases use : i<(if side then 2*q.h else 4*m)
  · cases side
    · let j : Fin (4*m):=⟨i,use⟩
      have rd:=q.selected_demand_width saved limits body y J mode atParty portFit kernel rowPtr arrays tileFit histFit
        reg enabled nd j banks lanes q.old_width_fits
      change (physicalWidth J mem false j.val).val≤J.party.V
      rw [rd]
      exact (q.input.width_le_maxWidth ((StageAddress.refreshEdge (splitWord q.s q.rem) (tagOrdinal q.s).symm).symm
        (addr (arrival actualG (tagOrdinal q.s).symm) actualZ (denseOrder pt j).val.1))).trans oldMax
    · let j : Fin (2*q.h):=⟨i,use⟩
      let a := (sparseOrder q.mult q.sym q.rowSum pt j).val.1
      let edge := refreshSlots (numbering q.mult q.rowSum) q.pad (.inl (.inr ⟨actualZ,a⟩))
      have cap := ((refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn).next q.branch).width_le_maxWidth edge
      change freshWidth q.mult q.rowSum (termWidth q.mult actualW actualSp) q.pad edge≤_ at cap
      have rd:=q.selected_supply_width saved limits body y J mode kernel arrays reg enabled ns j degree
        (q.selected_width_fits y a)
      change (physicalWidth J mem true j.val).val≤J.party.V
      rw [rd]
      simpa [edge,freshWidth,termWidth,a] using cap.trans newMax
  · have ext:=reg.extent
    dsimp only [HistoryPortCatalogue.stride] at ext
    have fit : i<2^W := by cases side <;> dsimp [cap] at hi <;> omega
    have n : side.toNat<HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap := by
      cases side <;> simp [HistoryPortCatalogue.stride]; omega
    have off : ¬portActive J mem side i := by
      intro used
      have h:=((portActive_iff J mem side i fit).1 used).2
      rw [reg.word side.toNat n] at h
      cases side <;> simp [issuedParty,HistoryPortCatalogue.Page.at,Party.ofTile] at h use <;> omega
    simp [physicalWidth,off]

/-- The real checked-plus-payload leaf publishes the exact gather map length.
The second info word is unchanged throughout source scanning. -/
theorem map_size_from_pair (node size : ℕ)
    (atNode : (HistoryNodePorts.id J.nodePorts).value (fun _=>0) mem (fun _=>0)=(node:Word W))
    (armed : partyActive J mem) (fit : HistoryPartyPair.atPair J.party node 1+1<2^W)
    (length : mem (HistoryPartyPair.atPair J.party node 1+1)=(size:Word W)) (sizeFit : size<2^W) :
    (partyMapCount J mem).val=size := by
  have base : (HistoryGatherBody.selected J mem).privatePage 1=(HistoryPartyPair.atPair J.party node 1:Word W) := by
    simp [HistoryGatherBody.selected,HistoryPartyPair.atPair,HistoryScratch.atWord,atNode,Nat.cast_add,Nat.cast_mul]
  simp only [partyMapCount,ite_eq_left armed,wordAt,base,←Nat.cast_add,Fin.val_cast_of_lt fit,length,Fin.val_cast_of_lt sizeFit]

open HistoryContraction HistogramTileNetwork Expander LinearAlgebra.SpectralBooks
variable {Pins : Type}
  (prior : WordLayout (oldPortGraph (arrival (refreshBinaryGraph q.input) (tagOrdinal q.s).symm))
    (refreshBinaryInput q.input) Pins)
  (next : WordLayout (actualPortGraph (outputGraph (refreshBinaryGraph q.input) q.mult q.sym q.rowSum q.noLoop q.hm q.pad))
    (freshWidth q.mult q.rowSum (termWidth q.mult (refreshBinaryInput q.input)
      (q.tile.widths (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input)
        (refreshBinaryBranchOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch))) q.pad) Pins)
local notation "owner" => (@id ((q.input.Base×BitWord q.rem)×Fin m))
local notation "count" => (fun _ : (q.input.Base×BitWord q.rem)×Fin m=>1)
local notation "ordered" => (@singleChild ((q.input.Base×BitWord q.rem)×Fin m))
local notation "here" => (actualZ,pt)
local notation "prevPin" => WordLayout.oldPin prior next owner count ordered here ⟨here,rfl⟩
local notation "nextPin" => WordLayout.newPin prior next owner count ordered here

/-- Literal directory and prefix cells from the sole chronological child and
the published refreshed half table. Every bit scan uses these same two tables. -/
structure GatherCells (J : HistoryGatherBody.Layout) (scratch : Memory W) (supply : Bool) (j bit : ℕ) where
  previous : RefreshOld (layoutOf (sourceRegisters J scratch supply j (bit:Word W))) (fun a=>(scratch a).val)
  successor : RefreshNew (layoutOf (sourceRegisters J scratch supply j (bit:Word W))) (fun a=>(scratch a).val)
  start : previous.start=WordLayout.childStart prior owner count ordered here ⟨here,rfl⟩
  before : (layoutOf (sourceRegisters J scratch supply j (bit:Word W))).oldBits=WordLayout.prior prior owner count ordered here
  oldHalfStarts : ∀e:(oldPortGraph π).Port here,(scratch (previous.table+(4*oldHalf π actualZ pt e+3))).val=prior.ports.start here e
  newHalfStarts : ∀e:(actualPortGraph (outputGraph actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad)).Port here,
    (scratch (successor.table+(4*physicalHalf (outputGraph actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad)
      e.val.1 e.val.2+3))).val=next.ports.start here e
  children : (layoutOf (sourceRegisters J scratch supply j (bit:Word W))).childIDs<2^W ∧ (layoutOf (sourceRegisters J scratch supply j (bit:Word W))).nodes+(8*previous.child+6)<2^W ∧ previous.header+1<2^W ∧ (layoutOf (sourceRegisters J scratch supply j (bit:Word W))).childStarts<2^W
  freshHeader : (layoutOf (sourceRegisters J scratch supply j (bit:Word W))).newHalves+1<2^W
  oldEnds : ∀f,f<2*m→previous.table+(4*f+3)<2^W
  newEnds : ∀f,f<2*deg→successor.table+(4*f+3)<2^W


/-- A real directory row and the issued half-edge arrays supply every entry
of the gather for both kinds of ports. The two order equalities identify
the chronological half indices with the order used by the physical stage. -/
def GatherCells.of_rows (J : HistoryGatherBody.Layout) (scratch : Memory W) (side : Bool) (slot bit : ℕ)
    (child : q.input.Site) {safe : ℕ→Prop} (small : ∀i,safe i→i<2^W)
    (rowsOld : State.HalfRows q.old safe (fun a=>(scratch a).val))
    (rowsNew : State.HalfRows q.step.sites safe (fun a=>(scratch a).val))
    (oldOrd : ∀e:(oldPortGraph π).Port here,∃j:Fin (2*m),j.val=oldHalf π actualZ pt e ∧
      ShrinkStage.Halves.prefixValue q.input.graph q.input.width (q.input.chart.symm child) j=prior.ports.start here e)
    (newOrd : ∀e:(actualPortGraph (outputGraph actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad)).Port here,
      ∃j:Fin (2*q.degree),j.val=physicalHalf (outputGraph actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad) e.val.1 e.val.2 ∧
      ShrinkStage.Halves.prefixValue (q.move.next q.term).graph (q.move.next q.term).width
        ((q.move.next q.term).chart.symm y) j=next.ports.start here e)
    (childDir : (scratch (selected J scratch).childIDs.val).val=q.old.id child)
    (cacheDir : (scratch ((J.nodePorts.nodes:Word W).val+(8*q.old.id child+6))).val=
      q.old.layer.incident+(q.old.ord child).val*2)
    (starts : scratch (J.nodePorts.starts:Word W).val=0)
    (countOld : (selected J scratch).oldBits.val=prior.ports.halfBits here)
    (newDir : (selected J scratch).newHalves.val=q.step.sites.layer.incident+(q.step.sites.ord y).val*2)
    (cacheFit : (J.nodePorts.nodes:Word W).val+(8*q.old.id child+6)<2^W) :
    q.GatherCells y prior next J scratch side slot bit := by
  let oldHd:=q.old.layer.incident+(q.old.ord child).val*2
  let newHd:=q.step.sites.layer.incident+(q.step.sites.ord y).val*2
  let M:=fun a=>(scratch a).val
  let T:=layoutOf (sourceRegisters J scratch side slot (bit:Word W))
  have h1:T.childIDs=(selected J scratch).childIDs.val:=rfl
  have h2:T.newHalves=newHd:=newDir
  have base:T.childStarts=(J.nodePorts.starts:Word W).val:=rfl
  have tiny:WordLayout.childStart prior owner count ordered here ⟨here,rfl⟩=0:=by
    change (∑ _ : Fin 0, prior.ports.halfBits here) = 0
    exact Fin.sum_univ_zero _
  have first : WordLayout.prior prior owner count ordered here=prior.ports.halfBits here:=by
    simp [WordLayout.prior,RefreshTies.singleChild]
  let O : RefreshOld T M:=⟨q.old.id child,oldHd,M (oldHd+1),0,childDir,cacheDir,rfl,by
    change (scratch (J.nodePorts.starts:Word W).val).val=0;rw [starts];rfl⟩
  let N : RefreshNew T M:=⟨M (newHd+1),by rw [h2]⟩
  have oldHeader : oldHd+1<2^W:=small _ (rowsOld.headerSafe child (1:Fin 2))
  have newHeader : newHd+1<2^W:=small _ (rowsNew.headerSafe y (1:Fin 2))
  refine ⟨O,N,tiny.symm,countOld.trans first.symm,?_,?_,⟨Fin.isLt _,cacheFit,oldHeader,Fin.isLt _⟩,h2 ▸ newHeader,?_,?_⟩
  · intro e
    obtain ⟨j,id,prefixValue⟩:=oldOrd e
    have rd:=rowsOld.start child j
    rw [id] at rd
    exact (show M (O.table+(4*oldHalf π actualZ pt e+3))=_
      from by simpa only [O,M,oldHd,Nat.add_assoc] using rd).trans prefixValue
  · intro e
    obtain ⟨j,id,prefixValue⟩:=newOrd e
    have rd:=rowsNew.start y j
    rw [id] at rd
    exact (show M (N.table+(4*physicalHalf (outputGraph actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad) e.val.1 e.val.2+3))=_
      from by simpa only [N,M,newHd,Nat.add_assoc] using rd).trans prefixValue
  · intro f hf
    have valid:=small _ (rowsOld.entriesSafe child ⟨f,hf⟩ (3:Fin 4))
    simpa only [O,M,oldHd,Fin.val_mk,show (3 : Fin 4).val = 3 from rfl,Nat.add_assoc] using valid
  · intro f hf
    have lim:f<2*q.degree:=q.degreeEq ▸ hf
    have valid:=small _ (rowsNew.entriesSafe y ⟨f,lim⟩ (3:Fin 4))
    simpa only [N,M,newHd,Fin.val_mk,show (3 : Fin 4).val = 3 from rfl,Nat.add_assoc] using valid

private theorem degree_prefix {F:Type} [Field F] {d l D E t : ℕ} {X:State d l} (e:D=E)
    (R:Move F X D t) (b:Fin R.rules.count)
    (y:((Program.recastMove e R).next (Program.degreeTerm e R b)).Site) (j:Fin (2*D)) :
    let X':=(Program.recastMove e R).next (Program.degreeTerm e R b)
    let tr:=(Equiv.cast (congrArg HistoryContraction.Shape.Site (R.target_eq b)))
      (Program.degreeTarget e R b (Move.WordStep.targetSite (R:=Program.recastMove e R) (i:=Program.degreeTerm e R b) y))
    ShrinkStage.Halves.prefixValue X'.graph X'.width (X'.chart.symm y)
      (Fin.cast (congrArg (2*·) e) j)=
    ShrinkStage.Halves.prefixValue (R.next b).graph (R.next b).width ((R.next b).chart.symm tr) j := by
  cases e
  let target := Equiv.cast (congrArg HistoryContraction.Shape.Site (R.target_eq b))
  exact congrArg (fun v : (R.next b).Site =>
    ShrinkStage.Halves.prefixValue (R.next b).graph (R.next b).width ((R.next b).chart.symm v) j)
    (target.apply_symm_apply y).symm

local notation "R₀" => refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn
local notation "I" => StageAddress.refreshInputIso q.input.graph q.input.chart (splitWord q.s q.rem) (tagOrdinal q.s).symm q.input.width
local notation "childSite" => (I).site.symm here
local notation "newState" => (R₀).next q.branch

set_option maxRecDepth 16000 in
set_option maxHeartbeats 600000 in
omit [Fintype F] in
/-- The old and fresh pins of this refresh both index the combined boundary
of its one predecessor and its actual successor vertex. -/
theorem gather_arg_room (L : q.input.Words Pins) (ord : q.input.OrderedHalves L)
    (age : 16≤u) (oldDegree : m≤volume u) (newDegree : 1+q.h+q.pad≤volume u)
    (oldMax : q.input.maxWidth≤volume u) (newMax : (newState).maxWidth≤volume u) :
    2+WordLayout.argSize ((I).pushWord L) ((newState).halfWords Pins) owner count ordered here≤2^W := by
  let V:=volume u
  have width (e : q.input.shape.Edge) : q.input.width e=actualW ((I).edge e) := by
    exact congrArg q.input.width ((StageAddress.refreshEdge (splitWord q.s q.rem)
      (tagOrdinal q.s).symm).symm_apply_apply e).symm
  have old:=(I).pushWord_halfBits_at L width here
  have oldWords : ((I).pushWord L).ports.halfBits here≤2*m*q.input.maxWidth :=
    (old.trans (ord.halfBits_eq_incident childSite)).le.trans (q.input.incidentWidth_le childSite)
  have nextWords : ((newState).halfWords Pins).ports.halfBits here≤2*(1+q.h+q.pad)*(newState).maxWidth :=
    (((newState).halfWords_ordered Pins).halfBits_eq_incident here).le.trans ((newState).incidentWidth_le here)
  have first : WordLayout.prior ((I).pushWord L) owner count ordered here=((I).pushWord L).ports.halfBits here:=by
    simp [WordLayout.prior,RefreshTies.singleChild]
  have mul {d width : ℕ} (hd : d ≤ V) (hw : width ≤ V) : 2*d*width ≤ 2*V^2:=by
    calc
      _ ≤ 2*V*V:=Nat.mul_le_mul (Nat.mul_le_mul_left _ hd) hw
      _ = _ := by ring
  have o:=oldWords.trans (mul oldDegree oldMax)
  have n:=nextWords.trans (mul newDegree newMax)
  have big:1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have small:V≤V^2:=Nat.le_self_pow (by decide) _
  have room:=Nat.mul_le_mul_right (V^2) (show 8≤V^2 by omega)
  rw [show V^2*V^2=V^4 by ring] at room
  have word:=TickWorkspace.word_space (i:=0) (u:=u) (by omega)
    (by change 0<V^4;exact Nat.pow_pos (show 0<V by omega))
  change TickWorkspace.base u 0+V^4<2^W at word
  have size : WordLayout.argSize ((I).pushWord L) ((newState).halfWords Pins) owner count ordered here =
      ((I).pushWord L).ports.halfBits here + ((newState).halfWords Pins).ports.halfBits here :=
    congrArg (fun n : ℕ => n + ((newState).halfWords Pins).ports.halfBits here) first
  exact (Nat.add_le_add_left size.le 2).trans (by omega)


private theorem degree_prefix_at {F : Type} [Field F] {d l D E t : ℕ} {X : State d l}
    (e : D=E) (R : Move F X D t) (b : Fin R.rules.count)
    (y : ((Program.recastMove e R).next (Program.degreeTerm e R b)).Site) (j : Fin (2*D))
    (v : (R.next b).Site) (value : ℕ)
    (site_eq : (Equiv.cast (congrArg HistoryContraction.Shape.Site (R.target_eq b)))
      (Program.degreeTarget e R b (Move.WordStep.targetSite (R:=Program.recastMove e R)
        (i:=Program.degreeTerm e R b) y))=v)
    (read : ShrinkStage.Halves.prefixValue (R.next b).graph (R.next b).width
      ((R.next b).chart.symm v) j=value) :
    let nextState := (Program.recastMove e R).next (Program.degreeTerm e R b)
    ShrinkStage.Halves.prefixValue nextState.graph nextState.width (nextState.chart.symm y)
      (Fin.cast (congrArg (2*·) e) j)=value :=
  (degree_prefix e R b y j).trans ((congrArg (fun x : (R.next b).Site =>
    ShrinkStage.Halves.prefixValue (R.next b).graph (R.next b).width ((R.next b).chart.symm x) j)
    site_eq).trans read)

open private cast_site_self from OAI.ThreeFlat.RAM.HistoryMotifTariffRefreshEntry

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1400000 in
omit [Fintype F] in
/-- The archived predecessor and successor half orders agree with the particular
word layouts used by the issued refresh tree, also after the degree transport. -/
theorem issued_prefix_orders (L : q.input.Words Pins) (orderedPrior : q.input.OrderedHalves L) :
    (∀e:(oldPortGraph π).Port here,∃j:Fin (2*m),j.val=oldHalf π actualZ pt e ∧
      ShrinkStage.Halves.prefixValue q.input.graph q.input.width (q.input.chart.symm childSite) j=
        ((I).pushWord L).ports.start here e) ∧
    (∀e:(actualPortGraph (outputGraph actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad)).Port here,
      ∃j:Fin (2*q.degree),j.val=physicalHalf (outputGraph actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad) e.val.1 e.val.2 ∧
      ShrinkStage.Halves.prefixValue (q.move.next q.term).graph (q.move.next q.term).width ((q.move.next q.term).chart.symm y) j=
        ((newState).halfWords Pins).ports.start here e) := by
  constructor
  · intro port
    let ord:=oldHalf π actualZ pt port
    have lt:ord<2*m:=by
      obtain ⟨⟨e,side⟩,pr⟩:=port
      cases side <;> simp only [ord,oldHalf,Bool.false_eq_true,ite_false,ite_true] <;>
        first | omega
    let i:Fin (2*m):=⟨ord,lt⟩
    exact ⟨i,rfl,predecessor_prefix q.input L orderedPrior (splitWord q.s q.rem) (tagOrdinal q.s).symm here port i rfl⟩
  · intro port
    let freshWords:=(newState).halfWords Pins
    let i:=((freshWords.order here).symm port).cast (((newState).halfWords_ordered Pins).count here)
    have n:i.val=physicalHalf (outputGraph actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad) port.val.1 port.val.2 :=
      ordered_ordinal (newState) freshWords ((newState).halfWords_ordered Pins) here port
    refine ⟨Fin.cast (congrArg (2*·) q.degreeEq) i,n,?_⟩
    have siteCoordinates : q.typedKernelSite y=here :=
      Prod.ext (q.chosenBlock_coordinates y).1.symm (q.chosenBlock_coordinates y).2.symm
    have siteEq := (cast_site_self ((q.input.Base × BitWord q.rem) × Fin (2^q.s))
      (congrArg HistoryContraction.Shape.Site ((R₀).target_eq q.branch)) (q.typedKernelSite y)).trans siteCoordinates
    have read := ordered_prefix (newState) freshWords ((newState).halfWords_ordered Pins) here port i n
    exact degree_prefix_at q.degreeEq (R₀) q.branch y i here (freshWords.ports.start here port) siteEq read

/-- The literal tables used in a selected prefix/fresh pin lookup, specialized
to the current chronological word layout at its true single predecessor. -/
def issued_gather_cells (L : q.input.Words Pins) (orderedPrior : q.input.OrderedHalves L)
    (J : HistoryGatherBody.Layout) (scratch : Memory W) (side : Bool) (slot bit : ℕ)
    {safe : ℕ→Prop} (small : ∀i,safe i→i<2^W)
    (oldRows : State.HalfRows q.old safe (fun a=>(scratch a).val))
    (newRows : State.HalfRows q.step.sites safe (fun a=>(scratch a).val)) :=
  let orders:=q.issued_prefix_orders y L orderedPrior
  GatherCells.of_rows q y ((I).pushWord L) ((newState).halfWords Pins) J scratch side slot bit
    childSite small oldRows newRows orders.1 orders.2


omit [Fintype F] in
private theorem child_table_end :
    q.entry.words 42+Fintype.card q.input.Base*m*2^q.rem≤q.entry.next.heap := by
  let N:=Fintype.card q.input.Base*m*2^q.rem
  have spans := RefreshNodeOwners.owner_spans (c:=q.cursor) (v:=Fintype.card q.input.Base)
    (a:=q.s) (t:=q.rem) (h:=q.h) (pad:=q.pad) (K:=K)
  have left : q.entry.words 42+N=q.entry.words 44 := spans.1
  have right : q.entry.words 44+N=q.entry.next.heap := spans.2.1
  exact left.le.trans ((Nat.le_add_right _ N).trans right.le)

include saved limits body in
omit [Fintype F] in
/-- The child pointer held in this refresh row is the single original input
site supporting the elected kernel, in the old physical layer's numbering. -/
theorem selected_child_id (fits : q.old.id childSite<2^W) :
    (mem (q.entry.words 42+ix)).val=q.old.id childSite := by
  have kernelOrd : (refreshFinalOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch here).val=ix := by
    change (Records.siteOrder ((q.input.order (actualZ).1,pt),(actualZ).2)).val=_
    rw [Records.siteOrder_val]
    simpa [chosenBlock] using q.kernelSite_index y
  have owned : (R₀).rules.owner q.branch childSite=here := (I).site.apply_symm_apply here
  have transpose:RefreshOwnership.child m (2^q.rem) ix=(refreshOldOrder q.input childSite).val := by
    have t:=(refresh_owner_ordinals q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch childSite).1
    rwa [owned,kernelOrd] at t
  have oldOrdinal:(refreshOldOrder q.input childSite).val=(q.old.ord childSite).val := by
    exact (RefreshStageLayout.pair_index q.input.order (tagOrdinal (q.s+q.rem))
      (q.input.chart.symm childSite)).trans (q.numbered childSite).symm
  let N:=Fintype.card q.input.Base*m*2^q.rem
  have inRange:ix<N:=by
    have t:=(Records.siteOrder z).isLt
    rwa [Records.siteOrder_val,q.kernelSite_index] at t
  have high : q.cursor.heap≤q.entry.words 42:=(RefreshNodeOwners.owner_spans (c:=q.cursor)
    (v:=Fintype.card q.input.Base) (a:=q.s) (t:=q.rem) (h:=q.h) (pad:=q.pad) (K:=K)).2.2.1
  have hi:q.entry.words 42+ix<bound:=(Nat.add_lt_add_left inRange _).trans_le (child_table_end q)
  have lo:endHeaders≤q.entry.words 42+ix:=limits.1.trans (high.trans (Nat.le_add_right _ _))
  have below:=hi.trans_le limits.2.1
  have rd : q.out (q.entry.words 42+ix)=(q.cursor.node:Word W)+(RefreshOwnership.child m (2^q.rem) ix:Word W) :=
    q.issued.child (⟨ix,inRange⟩ : Fin N)
  have number : q.cursor.node+RefreshOwnership.child m (2^q.rem) ix=q.old.id childSite :=
    congrArg₂ Nat.add q.first.symm (transpose.trans oldOrdinal)
  have encoded : (q.cursor.node:Word W)+(RefreshOwnership.child m (2^q.rem) ix:Word W)=
      ((q.cursor.node+RefreshOwnership.child m (2^q.rem) ix:ℕ):Word W) :=
    (Nat.cast_add _ _).symm
  have stored : mem (q.entry.words 42+ix)=(q.old.id childSite:Word W) :=
    (body _ (.inr lo) hi).trans ((saved _ below.ne (below.trans limits.2.2).ne (.inr lo) hi).trans
      (rd.trans (encoded.trans (congrArg (fun n : ℕ => (n:Word W)) number))))
  exact (congrArg Fin.val stored).trans (Fin.val_cast_of_lt fits)

include saved limits body in
omit [Fintype F] in
/-- The old and new directory pointers used at every port read, including
the one saved nonzero prefix for the singleton child. -/
theorem selected_node_cells (J : HistoryGatherBody.Layout) (banks : NavigationNodeRows.Banks)
    (nodes : J.nodePorts.nodes=banks.nodes)
    (cursor : (HistoryNodePorts.id J.nodePorts).value (fun _=>0) mem (fun _=>0)=(q.step.sites.id y:Word W))
    (oldRow : HistoryStageSetup.DirectoryRow banks q.old.layer (q.old.ord childSite) mem)
    (newRow : HistoryStageSetup.DirectoryRow banks q.step.sites.layer (q.step.sites.ord y) mem)
    (endOld : q.old.id childSite<2^W) (nodeFit : banks.nodes+8*q.step.sites.id y+6<2^W)
    (cacheFit : banks.nodes+8*q.old.id childSite+6<2^W) (nodeBank : banks.nodes<2^W)
    (startsFit : J.nodePorts.starts+1<2^W) (starts : mem J.nodePorts.starts=0)
    (oldSize : ℕ) (width : oldSize<2^W) (prefixCount : mem (J.nodePorts.starts+1)=(oldSize:Word W)) :
    (mem (selected J mem).childIDs.val).val=q.old.id childSite ∧
    (mem ((J.nodePorts.nodes:Word W).val+(8*q.old.id childSite+6))).val=
      q.old.layer.incident+(q.old.ord childSite).val*2 ∧
    mem (J.nodePorts.starts:Word W).val=0 ∧ (selected J mem).oldBits.val=oldSize ∧
    (selected J mem).newHalves.val=q.step.sites.layer.incident+ix*2 ∧
    (J.nodePorts.nodes:Word W).val+(8*q.old.id childSite+6)<2^W ↔
    q.old.layer.incident+(q.old.ord childSite).val*2<2^W ∧ q.step.sites.layer.incident+ix*2<2^W := by
  let oldHd:=q.old.layer.incident+(q.old.ord childSite).val*2
  let newHd:=q.step.sites.layer.incident+ix*2
  have degree:q.step.sites.layer.childCount=1:=by rw [q.issued_layer];rfl
  have ch:q.step.sites.layer.children=q.entry.words 42:=by rw [q.issued_layer];rfl
  have nodeVal:nodeWord J mem=(banks.nodes+8*q.step.sites.id y:ℕ):=by
    change (J.nodePorts.nodes:Word W)+8*((HistoryNodePorts.id J.nodePorts).value (fun _=>0) mem (fun _=>0))=_
    rw [cursor,nodes];simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have newCell (f : ℕ) (offsetBound : f ≤ 6) : ((nodeWord J mem+(f:Word W)).val)=banks.nodes+8*q.step.sites.id y+f:=by
    rw [nodeVal,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have parentKids : (selected J mem).childIDs=(q.entry.words 42+ix:ℕ):=by
    change mem (nodeWord J mem+3).val=_
    rw [show (3:Word W)=((3:ℕ):Word W) from rfl,newCell 3 (by decide)]
    simpa [State.ArchiveSites.id,degree,ch] using newRow.childPtr
  have table : (selected J mem).newHalves=(newHd:Word W):=by
    change mem (nodeWord J mem+6).val=_
    rw [show (6:Word W)=((6:ℕ):Word W) from rfl,newCell 6 (by decide)]
    exact newRow.incident
  have typ : (HistoryNodePorts.childCount J.nodePorts).value (fun _=>0) mem (fun _=>0)=(1:Word W):=by
    change mem (nodeWord J mem+4).val=_
    rw [show (4:Word W)=((4:ℕ):Word W) from rfl,newCell 4 (by decide),←Nat.cast_one]
    simpa [State.ArchiveSites.id,degree] using newRow.childCount
  have was : (selected J mem).oldBits.val=oldSize := by
    change (mem ((J.nodePorts.starts:Word W)+(HistoryNodePorts.childCount J.nodePorts).value (fun _=>0) mem (fun _=>0)).val).val=_
    have addr : (J.nodePorts.starts:Word W)+1=((J.nodePorts.starts+1:ℕ):Word W) := by
      simp only [Nat.cast_add,Nat.cast_one]
    rw [typ,addr,Fin.val_cast_of_lt startsFit,prefixCount,Fin.val_cast_of_lt width]
  have cache : mem ((J.nodePorts.nodes:Word W).val+(8*q.old.id childSite+6))=(oldHd:Word W) := by
    rw [nodes,Fin.val_cast_of_lt nodeBank]
    simpa only [State.ArchiveSites.id,Nat.add_assoc] using oldRow.incident
  have childFit:q.entry.words 42+ix<2^W:=by
    have n : ix<Fintype.card q.input.Base*m*2^q.rem := by
      have h:=(Records.siteOrder z).isLt
      rwa [Records.siteOrder_val,q.kernelSite_index] at h
    exact (Nat.add_lt_add_left n _).trans_le ((child_table_end q).trans (limits.2.1.trans cur.isLt.le))
  constructor
  · rintro ⟨_,a,_,_,b,_⟩
    exact ⟨a ▸ Fin.isLt _,b ▸ Fin.isLt _⟩
  · rintro ⟨hOld,hNew⟩
    refine ⟨?_,(congrArg Fin.val cache).trans (Fin.val_cast_of_lt hOld),?_,was,
      (congrArg Fin.val table).trans (Fin.val_cast_of_lt hNew),?_⟩
    · rw [parentKids,Fin.val_cast_of_lt childFit]
      exact q.selected_child_id saved limits body y endOld
    · rw [Fin.val_cast_of_lt (by omega)]
      exact starts
    · rw [nodes,Fin.val_cast_of_lt nodeBank]
      omega


include saved limits body in
/-- Compute every lookup cell from the actual terminal S44 rows, the old and
fresh compact half tables, and the two words published by this node's prefix
scan. The result is uniform in the bit and the direction chosen by S17. -/
def gather_cells_at (L : q.input.Words Pins) (orderedPrior : q.input.OrderedHalves L)
    (J : HistoryGatherBody.Layout) (banks : NavigationNodeRows.Banks) (side : Bool) (slot bit : ℕ)
    (nodes : J.nodePorts.nodes=banks.nodes)
    (cursor : (HistoryNodePorts.id J.nodePorts).value (fun _=>0) mem (fun _=>0)=(q.step.sites.id y:Word W))
    {safe : ℕ→Prop} (small : ∀i,safe i→i<2^W)
    (oldRows : State.HalfRows q.old safe (fun a=>(mem a).val))
    (newRows : State.HalfRows q.step.sites safe (fun a=>(mem a).val))
    (oldRow : HistoryStageSetup.DirectoryRow banks q.old.layer (q.old.ord childSite) mem)
    (newRow : HistoryStageSetup.DirectoryRow banks q.step.sites.layer (q.step.sites.ord y) mem)
    (endOld : q.old.id childSite<2^W) (nodeFit : banks.nodes+8*q.step.sites.id y+6<2^W)
    (cacheFit : banks.nodes+8*q.old.id childSite+6<2^W) (nodeBank : banks.nodes<2^W)
    (startsFit : J.nodePorts.starts+1<2^W) (starts : mem J.nodePorts.starts=0)
    (width : ((I).pushWord L).ports.halfBits here<2^W)
    (one : mem (J.nodePorts.starts+1)=(((I).pushWord L).ports.halfBits here:Word W)) :
    q.GatherCells y ((I).pushWord L) ((newState).halfWords Pins) J mem side slot bit := by
  have hOld:=small _ (oldRows.headerSafe childSite (0:Fin 2))
  have hNew:=small _ (newRows.headerSafe y (0:Fin 2))
  have reads := (q.selected_node_cells saved limits body y J banks nodes cursor oldRow newRow endOld nodeFit cacheFit
    nodeBank startsFit starts _ width one).2 ⟨by simpa using hOld,by simpa using hNew⟩
  exact q.issued_gather_cells y L orderedPrior J mem side slot bit small oldRows newRows reads.1 reads.2.1
    reads.2.2.1 reads.2.2.2.1 reads.2.2.2.2.1 reads.2.2.2.2.2

include saved limits body in
/-- Half tables and the directory are read in the original archive. Each
iteration writes only the port scratch, so both views are still valid. -/
def gather_cells_from_input (L : q.input.Words Pins) (orderedPrior : q.input.OrderedHalves L)
    (J : HistoryGatherBody.Layout) (banks : NavigationNodeRows.Banks)
    {page extent : ℕ} (window : q.PortWindow (endHeaders:=endHeaders) J mem page extent)
    (nodes : J.nodePorts.nodes=banks.nodes)
    (cursor : (HistoryNodePorts.id J.nodePorts).value (fun _=>0) mem (fun _=>0)=(q.step.sites.id y:Word W))
    {safe : ℕ→Prop} (small : ∀i,safe i→i<2^W)
    (away : ∀i,safe i→i<J.temp ∨ portsEnd J ≤ i)
    (oldRows : State.HalfRows q.old safe (fun a=>(mem a).val))
    (newRows : State.HalfRows q.step.sites safe (fun a=>(mem a).val))
    (oldRow : HistoryStageSetup.DirectoryRow banks q.old.layer (q.old.ord childSite) mem)
    (newRow : HistoryStageSetup.DirectoryRow banks q.step.sites.layer (q.step.sites.ord y) mem)
    (dirs : portsEnd J≤banks.nodes) (charges : portsEnd J≤banks.charges) (prefixStart : portsEnd J≤J.nodePorts.starts)
    (endOld : q.old.id childSite<2^W) (nodeFit : banks.nodes+8*q.step.sites.id y+6<2^W)
    (cacheFit : banks.nodes+8*q.old.id childSite+6<2^W) (nodeBank : banks.nodes<2^W)
    (startsFit : J.nodePorts.starts+1<2^W) (starts : mem J.nodePorts.starts=0)
    (width : ((I).pushWord L).ports.halfBits here<2^W)
    (one : mem (J.nodePorts.starts+1)=(((I).pushWord L).ports.halfBits here:Word W))
    (side : Bool) (slot bit : ℕ) (scratch : Memory W)
    (frame : DescriptorScan.agreesOutside J.temp (portsEnd J) scratch mem) :
    q.GatherCells y ((I).pushWord L) ((newState).halfWords Pins) J scratch side slot bit := by
  have stable (i:ℕ) (h:safe i) : (scratch i).val=(mem i).val:=congrArg Fin.val (frame i (away i h))
  have directory {l : NavigationNodeRows.Layer} {j : Fin l.count} (D : HistoryStageSetup.DirectoryRow banks l j mem) :
      HistoryStageSetup.DirectoryRow banks l j scratch :=
    D.retain (fun k _=>frame _ (.inr (by omega))) (frame _ (.inr (by omega)))
  exact q.gather_cells_at saved limits (fun i range hi=>(frame i (window.stageCells i range hi)).trans (body i range hi))
    y L orderedPrior J banks side slot bit nodes ((HistoryGatherBody.id_stable J (frame _ window.mask.cursor)).trans cursor)
    small (oldRows.transfer stable (fun _ h=>h)) (newRows.transfer stable (fun _ h=>h))
    (directory oldRow) (directory newRow) endOld nodeFit cacheFit nodeBank startsFit
    ((frame _ (.inr prefixStart)).trans starts) width ((frame _ (.inr (by omega))).trans one)

local notation "family" => DoublePorts.connectedSupply q.mult q.hh q.rowSum q.sym q.conn
local notation "dense" => RefreshMotif.denseGraph m
local notation "pp" => denseOrder pt
local notation "ss" => sparseOrder q.mult q.sym q.rowSum pt
local notation "bse" => q.tile.base choice
local notation "full" => profile actualG (tagOrdinal q.s).symm actualW actualZ
local notation "T₀" => q.tile.block choice
local notation "r₀" => refreshBinaryCopies q.tile q.input actualZ
local notation "h₀" => bh actualZ
local notation "k₀" => WordLayout.argSize prior next owner count ordered here

/-- Execute the actual selected refresh party's source gather from a mounted
S38 grid, the retained six-word incident and the chronological half prefixes. -/
abbrev emit_gather (B : Block F) {height start : ℕ} (mounted : Mounted B height W start mem)
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (kindBase : J.party.kinds=(refreshFamily B start height).kinds) (portBase : J.catalogue=(refreshFamily B start height).ports)
    (dem : J.demandCap=(refreshGrid B).demand) (sup : J.supplyCap=(refreshGrid B).supply) (dig : J.digitCap=(refreshGrid B).digits)
    (parties : J.party.parties=m) (enabled : partyActive J mem)
    (kindRoom : (refreshFamily B start height).kinds+7*((choice).val*m+(pt).val)+7≤2^W)
    (pgRoom : (refreshFamily B start height).ports+(refreshGrid B).stride*((choice).val*m+(pt).val)+(refreshGrid B).stride≤2^W)
    (kindFit : ∀ i:Fin 7,((issuedRecord).kind (arity B)).words i<2^W)
    (portWord : ∀ i:Fin (refreshGrid B).stride,(issuedRecord).port.at (refreshGrid B).demand (refreshGrid B).supply i.val<2^W)
    (banks : 3*m<2^W) (lanes : 2^q.rem<2^W) (degree : q.h<2^W) (small : 4≤2^W)
    (limitHalf : (P).halves+(Fintype.card q.input.Base*m*2^q.rem)*(2*deg)*4≤2^W) :=
  letI : Nonempty (Fin m):=⟨pt⟩
  letI := (T₀).hasLetter
  let reg:=q.selected_page saved limits body y J atParty rowPtr tileFit histFit B mounted supported
    kindBase portBase dem sup dig parties kindRoom pgRoom kindFit portWord
  let caps:=(refreshGrid B).caps (issued_party_rom B mounted q.tile supported q.hh q.rowSum q.sym q.conn choice pt).1
  have nd:4*m≤J.demandCap:=dem ▸ caps.1
  have ns:2*q.h≤J.supplyCap:=sup ▸ caps.2.1
  have digits:(∑ i,bse (pp i).val.1)≤J.digitCap:=dig ▸ caps.2.2
  let header : Header ((dense).Port pt) (T₀).Alphabet (fun a=>bse a.val.1) (T₀).bits (4*m):=⟨pp,(T₀).encode⟩
  let nextBit:=actualBit actualG q.mult q.sym q.rowSum q.noLoop q.hm q.pad bw nextPin
  let oldBit:=fun a b=>(.pin (demandPin π δ dest S actualW actualSp actualZ pt prevPin nextBit a b):BitSource 0 k₀)
  let newBit:=fun a b=>(.pin (sparsePin δ S actualW actualSp actualZ pt nextBit a b):BitSource 0 k₀)
  let wire:=partyPointer dense family pt bse full header ss (T₀).output h₀ oldBit newBit
  let source:=typedSources («W»:=W) J dense family pt bse full header ss (T₀).output h₀ oldBit newBit
  let base:=((selected J mem).privatePage 2).val
  let plan:=nativePlan J mem source (gatheredWord base (fun i=>BitLayout.sourceAddress (wire i)))
  let page:=(refreshFamily B start height).ports+(refreshGrid B).stride*((choice).val*m+(pt).val)
  let demWidth:=q.selected_demand_width saved limits body y J mode atParty portFit kernel rowPtr arrays tileFit histFit
    reg enabled nd
  let supWidth:=q.selected_supply_width saved limits body y J mode kernel arrays reg enabled ns
  let samples:=q.elected_at_entry saved limits (fun i lo hi=>body i (.inr (limits.1.trans lo)) hi) y tileFit histFit
  have copies : (wordAt mem (selected J mem).incident 3).val=r₀:=by
    have order:=q.record_interval .motif (Records.rowOrder deg .motif (z,(3 : Fin 6)))
    rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index] at order
    have hi:(P).motif+(ix*6+3)<bound:=order.2
    unfold wordAt
    rw [←Fin.cast_val_eq_self (selected J mem).incident,rowPtr,←Nat.cast_add,Fin.val_cast_of_lt (by have:=cur.isLt;omega)]
    exact samples 3
  let mapSize := r₀*((2*q.h)*(T₀).bits)+(r₀*header.arity+(2*q.h)*(r₀*(T₀).bitCap))
  fun (window : q.PortWindow (endHeaders:=endHeaders) J mem page (HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap))
      (fields : ∀(side:Bool) (j bit:ℕ) (scratch:Memory W),j<cap J side→bit<plan.width side j→
         DescriptorScan.agreesOutside J.temp (portsEnd J) scratch mem→q.GatherCells y prior next J scratch side j bit)
      positive (resident : portsEnd J<2^W) headRoom oldMax newMax
      (mapCount : (partyMapCount J mem).val=mapSize) (mapRoom : base+mapSize<2^W) range pairInfo keep clear headAddress scalar oldRoom newRoom=>
  have fits:=q.selected_port_fits saved limits body y J mode atParty portFit kernel rowPtr arrays tileFit histFit
    reg enabled nd ns banks lanes degree oldMax newMax
  have headerSafe:=q.header_window saved limits body y J mode atParty portFit kernel rowPtr arrays tileFit histFit reg
    enabled window nd ns banks lanes degree (by rw [header_size];omega) pairInfo
  let demanded:=fun (j:Fin (4*m)) (b:Fin (full (pp j).val.1)) scratch frame=>
    have width:=demWidth j banks lanes (q.old_width_fits)
    have bit : b.val<plan.width false j.val:=by change _<(physicalWidth J mem false j.val).val;rw [width];exact b.isLt
    have row:=j.isLt.trans_le nd
    have span:=beforePort_frame J plan mem false j.val row scratch (by
      change DescriptorScan.agreesOutside _ (_+(physicalWidth J mem false j.val).val) _ _
      rw [width];exact frame) headRoom fits
    let stable:=PortWindow.after_port q window reg enabled span
    let D:=fields false j.val b.val scratch row bit span
    let target:=demandLocation (h:=q.h) (pad:=q.pad) π actualW actualZ pt (pp j) b.val
    have liveBit : b.val < actualW (addr π actualZ (pp j).val.1) := b.isLt
    have low:target.scope=1→target.half<2*m:=by
      have portIndex := (pp j).val.1.2.2.isLt
      cases hs : (pp j).val.2 <;> cases hd : (pp j).val.1.1 <;>
        simp [target,demandLocation,hs,hd] <;> omega
    have high:target.scope=2→target.half<2*deg:=by
      cases hs : (pp j).val.2 <;> cases hd : (pp j).val.1.1 <;>
        simp [target,demandLocation,hs,hd]
    q.selected_demand_pin (hidden:=0) saved limits (fun a inRange above=>(stable.2.2.2.2 a inRange above).trans (body a inRange above))
      y J mode atParty portFit ((congrArg Fin.val stable.1).trans kernel) ((congrArg Fin.val stable.2.1).trans rowPtr)
      arrays tileFit histFit stable.2.2.1 stable.2.2.2.1 prevPin nextPin nd j b banks lanes small
      (by
        have inWidth : b.val < (physicalWidth J mem false j.val).val := by rw [width]; exact b.isLt
        have inPage := inWidth.trans_le (fits false j.val row)
        exact (Nat.add_lt_add_left inPage _).trans_le ((aperture J false j.val row).2.trans resident.le))
      D.previous D.successor (refresh_old_prefix (pad:=q.pad) actualG (tagOrdinal q.s).symm q.mult q.sym q.rowSum q.noLoop q.hm
        actualW actualSp prior next owner count ordered actualZ pt rfl D.previous D.start D.oldHalfStarts)
      (refresh_new_prefix (pad:=q.pad) actualG (tagOrdinal q.s).symm q.mult q.sym q.rowSum q.noLoop q.hm
        actualW actualSp prior next owner count ordered actualZ pt D.successor D.before D.newHalfStarts)
      (fun selected=>⟨D.children.1,D.children.2.1,D.children.2.2.1,D.oldEnds _ (low selected),D.children.2.2.2⟩)
      (fun selected=>⟨D.freshHeader,D.newEnds _ (high selected)⟩)
  let supplied:=fun (j:Fin (2*q.h)) (b:Fin (actualSp actualZ (ss j).val.1)) scratch frame=>
    have width:=supWidth j degree (q.selected_width_fits y (ss j).val.1)
    have bit : b.val<plan.width true j.val:=by change _<(physicalWidth J mem true j.val).val;rw [width];exact b.isLt
    have row:=j.isLt.trans_le ns
    have span:=beforePort_frame J plan mem true j.val row scratch (by
      change DescriptorScan.agreesOutside _ (_+(physicalWidth J mem true j.val).val) _ _
      rw [width];exact frame) headRoom fits
    let stable:=PortWindow.after_port q window reg enabled span
    let D:=fields true j.val b.val scratch row bit span
    q.selected_supply_pin (hidden:=0) saved limits (fun a inRange above=>(stable.2.2.2.2 a inRange above).trans (body a inRange above))
      y J mode ((congrArg Fin.val stable.1).trans kernel) arrays stable.2.2.1 stable.2.2.2.1 nextPin
      ns j b (q.selected_width_fits y (ss j).val.1) small degree
      (by
        have inWidth : b.val < (physicalWidth J mem true j.val).val := by rw [width]; exact b.isLt
        have inPage := inWidth.trans_le (fits true j.val row)
        exact (Nat.add_lt_add_left inPage _).trans_le ((aperture J true j.val row).2.trans resident.le)) D.successor
      (refresh_new_prefix (pad:=q.pad) actualG (tagOrdinal q.s).symm q.mult q.sym q.rowSum q.noLoop q.hm
        actualW actualSp prior next owner count ordered actualZ pt D.successor D.before D.newHalfStarts)
      limitHalf D.freshHeader (D.newEnds _ (by have:=(numbering q.mult q.rowSum
        (if (ss j).val.2 then DoublePorts.reverseArc q.mult q.sym (ss j).val.1 else (ss j).val.1)).2.isLt;split_ifs <;> omega))
  have copyFit (j : Fin (4*m)) : full (pp j).val.1≤bse (pp j).val.1*r₀:=q.tile.fits _ _
  have digit (j : Fin (4*m)) : bse (pp j).val.1*r₀≤2^W:=by
    have one : bse (pp j).val.1≤∑k : Fin (4*m),bse (pp k).val.1 :=
      Finset.single_le_sum (f:=fun k : Fin (4*m)=>bse (pp k).val.1) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
    have ar : bse (pp j).val.1≤header.arity:=by change _≤(T₀).bits+∑k,bse (pp k).val.1;omega
    have arityBound:=Nat.mul_le_mul_left r₀ ar
    rw [Nat.mul_comm (bse _)]
    have inMap : r₀*header.arity ≤ mapSize :=
      (Nat.le_add_right ..).trans (Nat.le_add_left ..)
    exact arityBound.trans (inMap.trans ((Nat.le_add_left ..).trans mapRoom.le))
  have executed:=emit_tile J mem dense family pt bse full T₀ pp ss Fin.val Fin.val h₀ oldBit newBit page (arity B) reg enabled copies
    nd ns digits positive resident headRoom fits mapCount mapRoom range headerSafe keep clear headAddress digit scalar
    (fun i=>supWidth i degree (q.selected_width_fits y (ss i).val.1))
    (fun i=>demWidth i banks lanes q.old_width_fits) oldRoom newRoom demanded supplied
  fun (node : ℕ) (baseEq : base=HistoryPartyPair.atPair J.party node 2)
      (countFits : r₀*((2*q.h)*(T₀).bits)+(r₀*header.arity+(2*q.h)*(r₀*(T₀).bitCap))≤J.party.V)
      (modeRef : J.mode=(kernelTemplate (refreshGrid B)).mode) =>
    let sameRate:=tile_partyMapRate J mem (gatheredWord base (fun i=>BitLayout.sourceAddress (wire i)))
      dense family pt bse full T₀ pp ss Fin.val Fin.val h₀ oldBit newBit (kernelTemplate (refreshGrid B))
      modeRef dem sup (arity B) page reg nd ns (fun i=>demWidth i banks lanes q.old_width_fits)
      (fun i=>supWidth i degree (q.selected_width_fits y (ss i).val.1)) copyFit mapCount
    let gridRate:=(party_rates_in_grid (refreshGrid B) issuedRecord
      (issued_party_rom B mounted q.tile supported q.hh q.rowSum q.sym q.conn choice pt).1).2
    show ∃paid : Plan W,(procedure W J).Exec mem (output J paid mem) (HistoryGatherExecution.tariff W J paid) ∧
      (∀j : Fin (r₀*((2*q.h)*(T₀).bits)+(r₀*header.arity+(2*q.h)*(r₀*(T₀).bitCap))),output J paid mem (HistoryPartyPair.atPair J.party node 2+j.val)=
        (BitLayout.sourceAddress (wire j):Word W)) ∧
      (∀side j,j<cap J side→paid.width side j≤J.party.V) ∧
      paid.gatherBase=HistoryPartyPair.atPair J.party node 2 ∧ paid.gatherCount≤J.party.V ∧
      HistoryGatherExecution.tariff W J paid≤partyMapRate (kernelTemplate (refreshGrid B)) issuedRecord*(1+r₀) ∧
      HistoryGatherExecution.tariff W J paid≤gridMapRate (refreshGrid B)*(1+r₀) from
    Exists.intro plan (And.intro executed.1 (And.intro (fun j=>by rw [←baseEq];exact executed.2 j)
      (And.intro fits (And.intro baseEq (And.intro ((show plan.gatherCount=mapSize from mapCount).le.trans countFits)
        (And.intro sameRate (sameRate.trans (Nat.mul_le_mul_right _ gridRate))))))))

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HistoryStageBody.Physical
open RAM.HistoryPartyBatchExec RAM.HistoryRefreshEmitter RAM.NavigationNodeRows HistoryStageSetup
open PhysicalStage NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F:Type} [Field F] [Fintype F] {u K heads:ℕ} {cur:Word (16*u^10)}
    (q:RefreshReceipt F K cur) (B:Block F) (height rom:ℕ) (b:Banks)
    (y:(q.move.next q.term).Site)
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "node" => q.step.sites.id y
local notation "fam" => refreshFamily B rom height
local notation "arc" => archive B rom height K
local notation "A" => layout u arc fam
local notation "P" => CursorSpace.recordPointers q.entry
local notation "pos" => (q.step.sites.ord y).val

/-- The live memory reads needed for the active party's two successive boots. -/
structure PartyImage (final now:Memory W) : Prop where
  resident : Mounted B height W rom now
  archive : ∀ x,heads≤x→x<q.entry.next.heap→now x=final x
  row : DirectoryRow b q.step.sites.layer (q.step.sites.ord y) now
  cursor : numeric now (TickWorkspace.base u 18)-1=node

/-- Restrict the real node frame to its four inputs, including both directory banks. -/
theorem PartyImage.keep {final now after:Memory W}
    (img : PartyImage (heads:=heads) q B height rom b y final now) (age:16≤u) (nr:node<V^2)
    (lib:rom+libraryWords B height≤TickWorkspace.base u 12 ∨ TickWorkspace.base u 19≤rom)
    (archiveHigh:TickWorkspace.base u 19≤heads) (nodes:TickWorkspace.base u 19≤b.nodes)
    (pairs:TickWorkspace.base u 19≤b.charges)
    (frame:∀ x,OutsideNode u node x→after x=now x) :
    PartyImage (heads:=heads) q B height rom b y final after := by
  have high (x:ℕ) (above:TickWorkspace.base u 19≤x) : after x=now x :=
    frame x (outside_of_region node age nr (.inr (.inl above)))
  refine ⟨mounted_kept node B img.resident age nr lib frame,?_,
    img.row.retain (fun j _=>high _ (by omega)) (high _ (by omega)),?_⟩
  · intro x lo hi
    exact (high _ (archiveHigh.trans lo)).trans (img.archive x lo hi)
  · simpa only [numeric,frame _ (outside_of_region node age nr (.inr (.inr (.inl rfl))))]
      using img.cursor

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1400000 in
/-- Replay the genuinely empty arms preceding this exact selected refresh vertex.
The resulting image is the `input` of the positive checks compiler. -/
theorem PartyImage.before_checks {final stage:Memory W}
    (img : PartyImage (heads:=heads) q B height rom b y final stage)
    {ctr:Word W} (saved:SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds:RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (supported:B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (baseNodes:b.nodes=TickWorkspace.base u 44) (baseCharges:TickWorkspace.base u 19≤b.charges)
    (age:16≤u) (nr:node<V^2) (lib:TickWorkspace.base u 19≤rom)
    (archHigh:TickWorkspace.base u 19≤heads)
    (motifs:0<(fam).motifs) (cap:((fam).motifs+2)*((fam).parties+2)*8*32≤V) (mask:2^(fam).parties<2^W)
    (lut:(arc).lut+1<2^W) (step:(arc).lutStride<2^W) (pages:(arc).pages<2^W)
    (pageStep:(arc).pageStride<2^W) (counts:(arc).counts+1<2^W)
    (lutAway:(arc).lut+2≤TickWorkspace.base u 14+2*V ∨ TickWorkspace.base u 14+2*V+26≤(arc).lut)
    (countsAway:(arc).counts+2≤TickWorkspace.base u 14+2*V ∨ TickWorkspace.base u 14+2*V+26≤(arc).counts)
    (header:3+5*(fam).demands+4*(fam).supplies≤V) (ports:HistoryGatherExecution.portsEnd A<2^W) :
    let v:=(q.kernelSite y).1.2
    let card:=(issued_party_rom B img.resident q.tile supported q.hh q.rowSum q.sym q.conn 0 v).2.1
    PartyImage (heads:=heads) q B height rom b y final
      (beforeWinner A node (Fin.cast card.symm v) (tag (K:=F)) stage) := by
  intro v card
  let win:=Fin.cast card.symm v
  have bound:=And.intro bounds.header bounds.controls
  have inc := RefreshReceipt.incidence_at_entry (q := q) (mem := stage) (final := final)
    (saved := saved) (bounds := bound) (retained := fun x lo => img.archive x (bounds.header.trans lo))
    fam card y b baseNodes img.row img.cursor mask
  obtain ⟨immutable,loc⟩:=q.incidence_geometry y age (archHigh.trans bounds.header) bounds.controls.1 nr
  have frame:=physical_before_winner arc fam win (tag (K:=F)) stage inc immutable loc age nr motifs cap mask
    lut step pages pageStep counts lutAway countsAway header ports
  apply PartyImage.keep q B height rom b y img age nr (.inr lib) archHigh _ baseCharges frame.2.2
  rw [baseNodes]
  unfold TickWorkspace.base
  omega

set_option maxRecDepth 10000 in
/-- The actual selected checks program publishes its own table, while
preserving all four resident inputs for the immediately following payload boot. -/
theorem PartyImage.after_checks {final:Memory W} (X:HistoryPartyBatchExec.Build W)
    (img:PartyImage (heads:=heads) q B height rom b y final X.input)
    (window:PartyWindow u X.layout) (nr:node<V^2)
    (lib:rom+libraryWords B height≤TickWorkspace.base u 12 ∨ TickWorkspace.base u 19≤rom)
    (archHigh:TickWorkspace.base u 19≤heads) (nodeHigh:TickWorkspace.base u 19≤b.nodes)
    (pairHigh:TickWorkspace.base u 19≤b.charges)
    {h p:ℕ} {arity:Fin (X.table.r+X.table.s)→ℕ}
    (N:∀ i,BitNetwork F (arity i)) (wire:∀ i,Fin (arity i)→BitSource h p)
    (cursor:X.layout.cursor=TickWorkspace.base u 18)
    (seed:X.layout.seed+37<2^W) (stream:X.table.stream=HistoryPartyBatch.dest X.layout X.checks node 0)
    (maps:X.table.maps=X.layout.maps) (n:X.count≤V)
    (rows:8*HistoryPartyTapeRun.batchRows X.table≤V) (pins:HistoryPartyTapeRun.batchPins X.table≤V) :
    PartyImage (heads:=heads) q B height rom b y final
      (X.published (HistoryPartyTapeRun.jobs (w:=W) X.table N wire (tag (K:=F)))) := by
  apply PartyImage.keep q B height rom b y img window.age nr lib archHigh nodeHigh pairHigh
  intro x safe
  exact (batch_outside_node X window safe N wire (tag (K:=F)) (by rw [cursor];exact img.cursor)
    stream maps n rows pins).keeps seed


end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.RAM.HistoryRefreshEmitter

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr PhysicalProcedure Diagonal.TickWorkspace
open HistoryGatherBody HistoryStageBody.Physical HistoryPartyBatchExec HistoryMotifJoin
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {u node:ℕ} (arch:Archive) (f:Family) (winner:Fin f.parties)
local notation "W₀" => 16*u^10
local notation "nodePtr" => base u 44+8*node
local notation "C" => withMotif (layout u arch f) 0

/-- The three dynamic tests in the final one-child checks/payload join
are all read from the native masked incidence entry after the party roster. -/
theorem IncidenceRead.root_fields {mem:Memory W₀} {kernelPtr incidentPtr:ℕ}
    (read : IncidenceRead u f node winner mem kernelPtr incidentPtr)
    (room : IncidenceRoom u node kernelPtr incidentPtr) (oneFit:1<2^W₀) :
    (HistoryNodePorts.id (C).nodePorts).value (fun _=>0) mem (fun _=>0)=(node:Word W₀) ∧
      (selected C mem).kernel=(kernelPtr:Word W₀) ∧
      (selected C mem).incident=(incidentPtr:Word W₀) ∧
      ((C).party.motif:Word W₀)<wordAt mem (selected C mem).kernel 3 ∧
      (wordAt mem (selected C mem).incident 5).val=2^winner.val := by
  have fit : (HistoryNodePorts.id (C).nodePorts).Fits W₀ (fun _=>0) (numeric mem) (fun _=>0):=
    ⟨⟨trivial,room.cursor⟩,trivial,(mem (base u 18)).isLt,oneFit⟩
  have v := Formula.value_eq_natural (HistoryNodePorts.id (C).nodePorts) (fun _=>0) (numeric mem) (fun _=>0) fit
  rw [word_numeric] at v
  have idx : (HistoryNodePorts.id (C).nodePorts).value (fun _=>0) mem (fun _=>0)=(node:Word W₀):=by
    exact v.trans (congrArg (fun n : ℕ => (n : Word W₀)) read.cursor)
  have nd : nodeWord C mem=((base u 44+8*node : ℕ):Word W₀):=by
    change (base u 44:Word W₀)+8*((HistoryNodePorts.id (C).nodePorts).value (fun _=>0) mem (fun _=>0))=_
    simp only [idx,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have plus (q t:ℕ) (h:q+t<2^W₀) : ((q:Word W₀)+(t:Word W₀)).val=q+t:=by
    rw [←Nat.cast_add,Fin.val_cast_of_lt h]
  have atNode : (nodeWord C mem+5).val=nodePtr+5:=by
    rw [nd]
    simpa only [Nat.cast_ofNat] using plus (base u 44+8*node) 5 room.node
  have ker : (selected C mem).kernel=(kernelPtr:Word W₀):=by
    change mem (nodeWord C mem+5).val=_;rw [atNode]
    apply Fin.ext
    exact read.kernel.trans (Fin.val_cast_of_lt (by have:=room.kernel;omega)).symm
  have get (t:ℕ) (h:kernelPtr+t<2^W₀) :
      ((selected C mem).kernel+(t:Word W₀)).val=kernelPtr+t:=by rw [ker];exact plus _ _ h
  have incAt : ((selected C mem).kernel+4).val=kernelPtr+4 := by
    simpa only [Nat.cast_ofNat] using get 4 room.kernel
  have countAt : ((selected C mem).kernel+3).val=kernelPtr+3 := by
    simpa only [Nat.cast_ofNat] using get 3 (by have:=room.kernel;omega)
  have inc : (selected C mem).incident=(incidentPtr:Word W₀):=by
    change mem ((selected C mem).kernel+4).val+(6*0:ℕ)=_
    rw [incAt];simp only [Nat.mul_zero,Nat.cast_zero,add_zero]
    apply Fin.ext;exact read.incident.trans (Fin.val_cast_of_lt (by have:=room.incident;omega)).symm
  have mx : ((selected C mem).incident+5).val=incidentPtr+5:=by rw [inc];exact plus _ 5 room.incident
  have one : 0<(wordAt mem (selected C mem).kernel 3).val:=by
    change 0<(mem ((selected C mem).kernel+3).val).val;rw [countAt];exact read.count
  have mask : (wordAt mem (selected C mem).incident 5).val=2^winner.val:=by
    change (mem ((selected C mem).incident+5).val).val=_;rw [mx];exact read.mask
  exact ⟨idx,ker,inc,one,mask⟩

end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.RAM.HistoryNodePorts

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr PhysicalProcedure HistoryPartyBatchExec
open scoped Classical Fin.CommRing
noncomputable section

/-- Decode the exact half-width read by the private history compiler from the
published directory and incident header. The last record is only required for
a nonempty incident table. -/
theorem archived_fresh {W:ℕ} (A:Layout) (S:HistoryStageRoot.Input) (m:Memory W)
    (current:numeric m A.cursor-1=S.id) (nodes:A.nodes=S.nodeBase)
    (cursorRoom:A.cursor<2^W) (wide:1<2^W)
    (nodeRoom:HistoryStageRoot.node S+6<2^W)
    (headerRoom:numeric m (HistoryStageRoot.node S+6)+1<2^W)
    (tailRoom:0<numeric m (numeric m (HistoryStageRoot.node S+6))→
      HistoryStageBounds.lastIncident S (numeric m)+3<2^W) :
    (fresh A).value (fun _=>0) m (fun _=>0)=(HistoryStageRoot.halfWidth S (numeric m):Word W) := by
  let rd (e:Formula 1) (k:ℕ):Formula 1:=.load (add e (.lit k))
  let num:=numeric m
  let ok (e:Formula 1):=e.Fits W (fun _=>0) num (fun _=>0)
  let n:=HistoryStageRoot.node S
  let H:=num (n+6)
  let last:=HistoryStageBounds.lastIncident S num
  let c:Formula 1:=.load (halves A)
  let loc:=add (rd (halves A) 1) (mul (.lit 4) (.cut c (.lit 1)))
  have nf:ok (node A):=⟨trivial,⟨trivial,⟨⟨trivial,cursorRoom⟩,trivial,(m _).isLt,wide⟩,trivial⟩,trivial⟩
  have v:(node A).natural W (fun _=>0) num (fun _=>0)=n:=by
    change A.nodes+8*(numeric m A.cursor-1)=S.nodeBase+8*S.id
    rw [current,nodes]
  have h:(halves A).natural W (fun _=>0) num (fun _=>0)=H:=by
    change num ((node A).natural _ _ _ _+6)=H;rw [v]
  have hf:ok (halves A):=⟨⟨nf,trivial,trivial⟩,by
    change (node A).natural _ _ _ _+6<2^W;rw [v];exact nodeRoom⟩
  have cf:ok c:=⟨hf,by
    rw [h]
    exact Nat.lt_trans (Nat.lt_succ_self H) headerRoom⟩
  have cv:c.natural W (fun _=>0) num (fun _=>0)=num H:=by change num ((halves A).natural _ _ _ _)=_;rw [h]
  have pf:ok (rd (halves A) 1):=⟨⟨hf,trivial,trivial⟩,by
    change (halves A).natural _ _ _ _+1<2^W;rw [h];exact headerRoom⟩
  have lf:ok loc:=⟨pf,⟨trivial,⟨cf,trivial,by rw [cv];exact (m H).isLt,wide⟩,trivial⟩,trivial⟩
  have lv:loc.natural W (fun _=>0) num (fun _=>0)=last:=by
    change num ((halves A).natural _ _ _ _+1)+4*(c.natural _ _ _ _-1)=last
    rw [h,cv];rfl
  have get (j:ℕ) (small:j≤3) (positive:0<num H):ok (rd loc j):=⟨⟨lf,trivial,trivial⟩,by
    change loc.natural _ _ _ _+j<2^W
    rw [lv]
    exact lt_of_le_of_lt (Nat.add_le_add_left small last) (tailRoom positive)⟩
  have fits:ok (fresh A):=by
    refine ⟨cf,trivial,by rw [cv];exact (m H).isLt,by change 0<2^W;omega,?_⟩
    change (if decide (c.natural W (fun _=>0) num (fun _=>0)=0) then True else
      ok (rd loc 3) ∧ ok (rd loc 2) ∧ True)
    rw [cv];by_cases empty:num H=0
    · simp [empty]
    · simpa [empty] using And.intro (get 3 (by decide) (Nat.pos_of_ne_zero empty))
        (And.intro (get 2 (by decide) (Nat.pos_of_ne_zero empty)) trivial)
  have eval:=Formula.value_eq_natural (fresh A) (fun _=>0) num (fun _=>0) fits
  have nv:(fresh A).natural W (fun _=>0) num (fun _=>0)=HistoryStageRoot.halfWidth S num:=by
    change (if decide (c.natural _ _ _ _=0) then 0 else num (loc.natural _ _ _ _+3)+num (loc.natural _ _ _ _+2))=_
    rw [cv,lv];simp only [decide_eq_true_eq];rfl
  rw [nv] at eval
  simpa only [num,word_numeric,Nat.cast_zero] using eval

end
end ThreeFlat.RAM.HistoryNodePorts

namespace ThreeFlat.RAM.HistoryRefreshEmitter

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr PhysicalProcedure HistoryPartyBatchExec
open HistoryGatherBody HistoryStageBody.Physical
open scoped Classical Fin.CommRing
noncomputable section

private theorem archived_node_id {W : ℕ} (ports : HistoryNodePorts.Layout) (mem : Memory W)
    (expected : ℕ) (current : numeric mem ports.cursor-1=expected)
    (size : 1<2^W) (cursor : ports.cursor<2^W) :
    (HistoryNodePorts.id ports).value (fun _=>0) mem (fun _=>0)=(expected : Word W) := by
  have fits : (HistoryNodePorts.id ports).Fits W (fun _=>0) (numeric mem) (fun _=>0) :=
    ⟨⟨trivial,cursor⟩,trivial,(mem _).isLt,size⟩
  have raw : (HistoryNodePorts.id ports).natural W (fun _=>0) (numeric mem) (fun _=>0)=expected :=
    current
  have read := Formula.value_eq_natural (HistoryNodePorts.id ports) (fun _=>0) (numeric mem) (fun _=>0) fits
  simpa only [word_numeric,Nat.cast_zero,raw] using read

/-- The bounded source decoder's child list, incident header, and predecessor
width read precisely the three entries at the current S44 row. -/
theorem selected_source_header {W:ℕ} (A:Layout) (T:HistoryStageRoot.Input) (mem:Memory W)
    (current:numeric mem A.nodePorts.cursor-1=T.id) (nodes:A.nodePorts.nodes=T.nodeBase)
    (size:1<2^W) (cursor:A.nodePorts.cursor<2^W)
    (nodeRoom:HistoryStageRoot.node T+6<2^W)
    (address:A.nodePorts.starts+numeric mem (HistoryStageRoot.node T+4)<2^W) :
    (selected A mem).childIDs=mem (HistoryStageRoot.node T+3) ∧
    (selected A mem).newHalves=mem (HistoryStageRoot.node T+6) ∧
    (selected A mem).oldBits=mem (A.nodePorts.starts+numeric mem (HistoryStageRoot.node T+4)) := by
  have v := archived_node_id A.nodePorts mem T.id current size cursor
  have natNode : nodeWord A mem=(HistoryStageRoot.node T:Word W):=by
    change (A.nodePorts.nodes:Word W)+8*((HistoryNodePorts.id A.nodePorts).value (fun _=>0) mem (fun _=>0))=_
    rw [v,nodes,HistoryStageRoot.node,Nat.cast_add,Nat.cast_mul];rfl
  have wordAtNode (k:ℕ) (small:k≤6) :
      mem (nodeWord A mem+(k:Word W)).val=mem (HistoryStageRoot.node T+k) := by
    rw [natNode,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have count : (HistoryNodePorts.childCount A.nodePorts).value (fun _=>0) mem (fun _=>0)=
      mem (HistoryStageRoot.node T+4):=wordAtNode 4 (by decide)
  exact ⟨wordAtNode 3 (by decide),wordAtNode 6 le_rfl,by
    change mem ((A.nodePorts.starts:Word W)+(HistoryNodePorts.childCount A.nodePorts).value _ mem _).val=_
    rw [count,show mem (HistoryStageRoot.node T+4)=(numeric mem (HistoryStageRoot.node T+4):Word W) by simp [numeric],
      ←Nat.cast_add,Fin.val_cast_of_lt address]⟩

/-- Numerical port arity in the singleton kernel header. The two terms are
the actual predecessor-prefix bank and the published positive/empty half tail. -/
theorem root_ports {W:ℕ} (A:Layout) (T:HistoryStageRoot.Input) (mem:Memory W)
    (n old fresh:ℕ) (current:numeric mem A.nodePorts.cursor-1=T.id) (nodes:A.nodePorts.nodes=T.nodeBase)
    (size:1<2^W) (cursor:A.nodePorts.cursor<2^W) (nodeRoom:HistoryStageRoot.node T+6<2^W)
    (headerRoom:numeric mem (HistoryStageRoot.node T+6)+1<2^W)
    (tailRoom:0<numeric mem (numeric mem (HistoryStageRoot.node T+6))→
      HistoryStageBounds.lastIncident T (numeric mem)+3<2^W)
    (degree:HistoryStageRoot.childCount T (numeric mem)=n) (address:A.nodePorts.starts+n<2^W)
    (childPrefix:mem (A.nodePorts.starts+n)=(old:Word W))
    (half:HistoryStageRoot.halfWidth T (numeric mem)=fresh) :
    (selected A mem).oldBits+(selected A mem).newBits=((old+fresh:ℕ):Word W) := by
  have v := archived_node_id A.nodePorts mem T.id current size cursor
  have natNode : nodeWord A mem=(HistoryStageRoot.node T:Word W):=by
    change (A.nodePorts.nodes:Word W)+8*((HistoryNodePorts.id A.nodePorts).value (fun _=>0) mem (fun _=>0))=_
    rw [v,nodes,HistoryStageRoot.node,Nat.cast_add,Nat.cast_mul];rfl
  have cnt : (HistoryNodePorts.childCount A.nodePorts).value (fun _=>0) mem (fun _=>0)=(n:Word W):=by
    change mem (nodeWord A mem+4).val=_
    rw [natNode,←Nat.cast_ofNat (R:=Word W) (n:=4),←Nat.cast_add,Fin.val_cast_of_lt (show HistoryStageRoot.node T+4<2^W by omega)]
    apply Fin.ext
    exact degree.trans (Fin.val_cast_of_lt (show n<2^W by omega)).symm
  have prior : (selected A mem).oldBits=(old:Word W):=by
    change mem ((A.nodePorts.starts:Word W)+(HistoryNodePorts.childCount A.nodePorts).value (fun _=>0) mem (fun _=>0)).val=_
    rw [cnt,←Nat.cast_add,Fin.val_cast_of_lt address,childPrefix]
  have next : (selected A mem).newBits=(fresh:Word W):=by
    change (HistoryNodePorts.fresh A.nodePorts).value (fun _=>0) mem (fun _=>0)=_
    rw [HistoryNodePorts.archived_fresh A.nodePorts T mem current nodes cursor size nodeRoom headerRoom tailRoom,half]
  rw [prior,next,Nat.cast_add]

end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
