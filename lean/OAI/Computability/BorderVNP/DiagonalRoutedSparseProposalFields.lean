import OAI.Computability.BorderVNP.DiagonalPaidReturnedSparseFields
import OAI.Computability.BorderVNP.DiagonalSparseReportOrdinals
import OAI.Computability.BorderVNP.DiagonalRoutedProposalGeometry
import OAI.Computability.BorderVNP.DiagonalReportSlottedPublication
import OAI.Computability.BorderVNP.DiagonalPrivatePathRead

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Sparse rows of an actual routed proposal before the argument computation -/

namespace Diagonal.ExternalSew

open VPVNP BurstRAM Crossing Packing Packing.CellAddresses Packing.CellAddressPhysical
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep FragmentRows TypedTaskBuilder SignedTaskArena
open BorderVNP.Cube Physical Physical.NativeAssignments DiagonalTallyAllocation DiagonalTallyCellReports ReportDirectory
open CompactMachine SparseExterior CellMacro.Generator CellSparse
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 7200

variable {D R r literalW link V g edges entries desc pred w J : ℕ}
    (a : SignedTaskArena.Layout) (N : Network D (FreeBlock R V) (fun _ => g))
    (cell : N.Site → Fin a.cube.cells) (edgeID : N.Edge ↪ Fin edges)
    (owners : (Cube.Packet a.cube.n a.cube.header.d a.cube.header.blocks → Selector a.cube.n a.cube.K a.cube.h) →
      Fin a.cube.header.d → Fin (R+1))
    (slot : LiveBit N cell ↪ Slot a.cube.n a.cube.header.d a.cube.header.blocks (a.cube.h*a.cube.b))
    (labels : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (charts : Fin (R+1) → ReportLayout) (home : Fin J → Fin a.cube.cells) (bundle : Fin J → ReportBundle)
    (supply wire : ℕ → ℕ) (pp lp : ℕ → ℕ × ℕ)

local notation3 (prettyPrint := false) "portEmbedding" =>
  (finProdFinEquiv.toEmbedding : FreeBlock R V ↪ Fin ((R+1)*V))
local notation3 (prettyPrint := false) "received" =>
  routedReceivedRows a.cube owners labels charts home bundle supply wire
local notation3 (prettyPrint := false) "fragmentOf(" p ", " r ")" =>
  FragmentRows.Layout.fromFrame (readings p 0) (readings (r).val.2.2)
local notation3 (prettyPrint := false) "controlScan(" u ", " p ", " o ", " c ", " l ", " n ")" =>
  a.controlRows (u).val (readings p 0) o c l n
local notation3 (prettyPrint := false) "endDataAt(" g ", " room ", " bits ", " v ")" =>
  Fragments.endData N cell edgeID portEmbedding (fillFree g room bits (fun _ => false))
    (routedEnds N cell owners slot v)

/-- The selected signed source fields are determined by the physical report and fragment emission alone.
The paid bound can use the ordering of the actual spans already returned by the raw publication. -/
theorem routedSparseFieldsBeforeArguments (place : LivePlacement N cell edgeID portEmbedding lp)
    (privateAfter : ∀ (out : ℕ → ℕ) (supplied : ℕ),
       (∀ c : Fin a.cube.cells,out (supplied+c.val)=suppliedSize N cell c) →
       ∀ j : Fin entries,out (supplied+(pp j.val).1)≤(pp j.val).2)
    (widthEq : ∀ c : Fin a.cube.cells, supply c.val=suppliedSize N cell c)
    (v : Routed (b:=a.cube.b) (s:=a.cube.s) owners) (u : Fin (R+1))
    (src : ∀ t, ReportAssignments (((received v)).cells t))
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank : RoutingISA.Bank w} {initial : Memory w}
    {banks : CellBanks.Layout} {cursor : ReportCursor}
    (report : Evaluator.Returns prepareCellReports pub mac bank initial)
    {ctl offsets liveBase portCount : ℕ}
    (hg : 0<g) (freeRoom : r*(2*literalW+R*link)≤V*g) (input : FreePort R r literalW → Bool)
    (seed : PreparedReportInput (l:=charts u) pub initial (((received v)).cells u) cursor ((freeDirectory R r literalW link
      V g entries desc)).description)
    (allocation : ReportAllocation a.before a.after banks (charts u) ((received v).cells u) cursor)
    (headers : CellPacket.WordsAt (readings initial) (charts u).headers (((received v).cells u).flatMap
      ReportCell.headerWords))
    (choice : (assignedReportReturnEquiv (w:=w) (l:=charts u) (cs:=(((received v)).cells u)) (q:=cursor)
      (description:=((freeDirectory R r literalW link V g entries desc)).description) (pub:=pub) (m:=initial) seed mac
        bank).symm report=src u)
    (fits : (fragmentOf(pub,report)).Fits w (readings report.val.2.2)) (cellsAt :
      a.fragments.cells=(fragmentOf(pub,report)).cells)
    (emission : SparseEmission a (fragmentOf(pub,report)) report.val.2.2 fits cellsAt)
    (ownerAfter : ∀ c : Fin a.cube.cells, (controlScan(u,pub,offsets,ctl,liveBase,portCount)).owner (readings
      emission.output) c.val=(((fun c : Fin a.cube.cells => owners v.1 (labels c (BorderVNP.Cube.Physical.chosen a.cube.b
      a.cube.s v.1)))) c).val)
    (bankStart : banks.bankStart=(a.cube).cellBank) (stride : banks.stride=(a.cube).cellStride)
    (wiring : Fragments.CableRows N cell edgeID portEmbedding (fragmentOf(pub,report)).host (readings report.val.2.2))
    (counts : ∀ c : Fin a.cube.cells, (readings report.val.2.2) ((fragmentOf(pub,report)).supplied+c.val)=suppliedSize N
      cell c)
    (bases : ∀ c : Fin a.cube.cells, (readings report.val.2.2)
      ((fragmentOf(pub,report)).host.cells+2*c.val+1)=(a.cube).cellBank+c.val*(a.cube).cellStride)
    (memories : Fin (R+1) → Memory w) (atTeam : memories u=report.val.2.2)
    (source : Fragments.SourceWords N cell edgeID portEmbedding hg freeRoom lp (a.cube).cellBank (a.cube).cellStride
      input (routedEnds N cell owners slot v) (fun c => readings (memories (((fun c : Fin a.cube.cells => owners v.1 (labels
        c (BorderVNP.Cube.Physical.chosen a.cube.b a.cube.s v.1)))) c))))
    {rawBase : ℕ} {placed : Memory w} {written : ℕ → ℕ} {I : Type*} [Fintype I]
    {host : I → Fin a.cube.cells} {index : I ↪ ℕ} {width : I → ℕ} {pinRegion : RoutingISA.Pins.Layout}
    (slotted : Evaluator.SlottedWriter a.cube (freeDirectory R r literalW link V g entries desc) pp lp pinRegion pub placed
      rawBase host index width)
    (retained : ReportWords a (readings pub 0) (readings (Directory.ISA.publish placed (readings pub 0) rawBase
      (((freeDirectory R r literalW link V g entries desc)).directory pp lp))) written (readings report.val.2.2) true)
    (arenaFit : (a.cube).stop<2^w)
    (packet : Fin ((received v).cells u).length → CellSparse.Directory) (pw : Fin ((received v).cells u).length → ℕ)
    (wordPos : 0<w) (wordFit : w≤pred+1) (scratch : a.p.scratchStride=SignedTaskArena.scratchWindow (pred+1))
    (pay : (∀ i : Fin ((received v).cells u).length, SparseExterior.Ordered ((readings report.val.2.2)
      ((fragmentOf(pub,report)).supplied+((received v).order ⟨u,i⟩).val)) 0
          (Fragments.spans ((fragmentOf(pub,report)).stream (readings report.val.2.2)) (endDataAt(hg,freeRoom,input,v))
            ((received v).order ⟨u,i⟩).val)) →
      (∀ i : Fin ((received v).cells u).length, (readings report.val.2.2) ((fragmentOf(pub,report)).supplied+((received
        v).order ⟨u,i⟩).val)=suppliedSize N cell ((received v).order ⟨u,i⟩)) →
      ∀ i, (CompactFrame.pack w (Packet.input (packet i) (pw i) ((⟨((src u).val.get (Fin.cast (src u).length.symm
        (i))).supplied,Fragments.spans ((fragmentOf(pub,report)).stream (readings report.val.2.2))
        (endDataAt(hg,freeRoom,input,v)) ((received v).order ⟨u,i⟩).val,((src u).val.get (Fin.cast (src u).length.symm
        (i))).bits⟩ : SparseExterior.Field)).bytes)).length≤TeamScales.width (pred+1) (1/2)) :
    let emitted := readings emission.output
    ∃ size : (controlScan(u,pub,offsets,ctl,liveBase,portCount)).before emitted
      (controlScan(u,pub,offsets,ctl,liveBase,portCount)).cells=((received v).cells u).length,
      ∃ rows : (i : Fin ((controlScan(u,pub,offsets,ctl,liveBase,portCount)).before emitted
        (controlScan(u,pub,offsets,ctl,liveBase,portCount)).cells)) → SparseCell a (fragmentOf(pub,report)) report.val.2.2
        (endDataAt(hg,freeRoom,input,v)) i.val,
        (∀ i,(rows i).number.val=globalCell (controlScan(u,pub,offsets,ctl,liveBase,portCount)).toLayout emitted i.val) ∧
        (∀ i,(rows i).number=((received v).order ⟨u,Fin.cast size i⟩) ∧ (rows i).tail=(((src u).val.get (Fin.cast (src
          u).length.symm (Fin.cast size i)))).bits) ∧
        (∀ i,(readings report.val.2.2) ((fragmentOf(pub,report)).supplied+(rows i).number.val)=supply (rows i).number.val) ∧
        ∀ i : Fin ((received v).cells u).length, let c := ((received v).order ⟨u,i⟩)
          ((emission.globalCells (a:=a) (team:=u.val) (frame:=(readings pub 0)) (offsets:=offsets) (ctl:=ctl)
            («live»:=liveBase)
            (ports:=portCount) rows c.val).field).values=List.ofFn ((pathSupply N cell edgeID portEmbedding owners slot
              (fillFree hg freeRoom input (fun _ => false)) v) c)++(((src u).val.get (Fin.cast (src u).length.symm
              (i)))).bits := by
  intro emitted
  obtain ⟨start,apart,len,wordsFit,ptr,counted,kept⟩ := retained.slottedPublication (a:=a) (freeDirectory R r literalW link
    V g entries desc) pp lp slotted rfl arenaFit
  have after := privateAfter (readings report.val.2.2) (fragmentOf(pub,report)).supplied counts
  let observed := fun c : Fin a.cube.cells => memories (((fun c : Fin a.cube.cells => owners v.1 (labels c
    (BorderVNP.Cube.Physical.chosen a.cube.b a.cube.s v.1)))) c)
  have ord := routed_emitted_ordinals a.cube owners labels charts home bundle supply wire v u
    (controlScan(u,pub,offsets,ctl,liveBase,portCount)) emitted ((received v).cells u)
    ⟨rfl,rfl⟩ rfl rfl ownerAfter
  obtain ⟨roster,eqLen,ordinal⟩ := ord
  have owns (i : Fin ((received v).cells u).length) :
      ((received v).order ⟨u,i⟩).val=(((src u).val.get (Fin.cast (src u).length.symm (i)))).number ∧ observed ((received
        v).order ⟨u,i⟩)=report.val.2.2 ∧
      (readings report.val.2.2) ((fragmentOf(pub,report)).host.cells+2*((received v).order ⟨u,i⟩).val+1)=(((src u).val.get
        (Fin.cast (src u).length.symm (i)))).external ∧ (readings report.val.2.2)
        ((fragmentOf(pub,report)).supplied+((received v).order ⟨u,i⟩).val)=(((src u).val.get (Fin.cast (src u).length.symm
        (i)))).supplied := by
    obtain ⟨number',external',supplied'⟩ := routedProposedCoordinates a.cube owners labels charts home bundle
      supply wire v u (src u) i
    have atOwner : (fun c : Fin a.cube.cells => owners v.1 (labels c (BorderVNP.Cube.Physical.chosen a.cube.b a.cube.s
      v.1))) ((received v).order ⟨u,i⟩)=u := receivedSourceRows_owner charts home bundle
      (fun c => owners v.1 (labels c (BorderVNP.Cube.Physical.chosen a.cube.b a.cube.s v.1)))
      (routedOwnerWord a.cube owners labels v) (routedOwnerWord_at a.cube owners labels v)
      (fun c => a.cube.cellBank+c*a.cube.cellStride) supply wire (fun _ _ _ _ => false) u i
    have key : observed ((received v).order ⟨u,i⟩)=report.val.2.2 := (congrArg memories atOwner).trans atTeam
    have naturalWidth := widthEq ((received v).order ⟨u,i⟩)
    exact ⟨number'.symm,key,(bases _).trans external'.symm,(counts _).trans (naturalWidth.symm.trans supplied'.symm)⟩
  obtain ⟨rows,indices,values⟩ := Fragments.paid_returned_sparse_fields (entries:=entries) («desc»:=desc)
    a N cell edgeID (readings pub 0) rawBase placed observed hg freeRoom pp lp place input (routedEnds N cell owners slot v)
      banks allocation seed headers
    report fits cellsAt emission (src u) choice (fun i => ((received v).order ⟨u,i⟩)) bankStart stride wiring counts after
      bases source start apart len
    wordsFit ptr counted kept packet pw (Nat.succ_pos pred) wordPos wordFit scratch roster ordinal owns
    (fun sorted => pay sorted (fun i => counts ((received v).order ⟨u,i⟩)))
  refine ⟨roster,rows,fun i => (congrArg Fin.val (indices i).1).trans (ordinal i),indices,?_,values⟩
  intro i
  exact (counts _).trans (widthEq (rows i).number).symm

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
