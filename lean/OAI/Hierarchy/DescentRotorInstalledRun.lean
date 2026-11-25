import OAI.Hierarchy.DescentRotorInstalledMatrix
import OAI.Hierarchy.DescentFallbackGLWindow

namespace OAI
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open DescentRotorWindowScore DescentPackedTicketChronology DescentPacking
open DescentRotorWindowArchive DescentCanonicalPorts
open DescentPackedRotorMatrix DescentResetTrunks DescentPackedResetRotorRoles
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentPacking.PackedMatch.Local.Gather DescentPackedZip DescentPackedFallbackTree.Image
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
local notation "native" => order.trans Fin.valEmbedding
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank groupKey ids)
local notation "c" => T.commonDepth
local notation "remain" => Z.k-c
local notation "Y" => 2^Z.n
local notation "L" => 2^(m-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "points" => Fin (L*(2*A.cap))
local notation "old" => Host J V k
local notation "here" => donor digits frm.basis fit
local notation "shelved" => signedPanel A native S ready names
local notation "short" => fun t=>shortName c (T.code t)
local notation "term" => fallbackCell A S ready digits Z T frm
local notation "bad" => exceptionalCell A S ready digits Z T frm
local notation "shape" => chartShape A S ready Z T
local notation "wireWord" => peerShapeWord A S ready digits Z T frm
local notation "arrive" => chartArrival A S ready native groupKey vertex
local notation "hostAt" => fun t=>frm.host.symm (T.code t).1
local notation "rootAt" => selectedRoot A S ready Z T
local notation "hs" => hostRoster A ids
local notation "ticketAt" => chartTicket A S ready digits native Z T frm groupKey vertex
local notation "rankAt" => leafRankAt A S ready Z T
variable (word : Host J V k → ℕ) (rank : Fin H→Fin (width (Z.k-T.commonDepth) (2^Z.n) A.degree)→Cell (Ht+2))


local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank
local notation "use" => useRotor Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old
local notation "endAt" => DescentIssuedFallbackPanel.endSite A
variable (room : ∀u,word u+1<2^field) (signBits : DescentSignedCableCodec.width A.degree A.cap≤field)
variable (onWire : ∀s : Bool, ∀e : Grain A,
  word (home A (DescentIssuedFallbackPanel.endSite A s e))=
    peerShapeWord A S ready digits Z T frm s (home A (DescentIssuedFallbackPanel.endSite A s e)))




variable (f B wire K : ℕ) (traffic : V→V→Block m→ℕ) (weight : V→Block m→ℕ)
variable (roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (vertex.trans Fin.valEmbedding) A.near Z.n f B wire K (fun v z i=>(traffic v z i:ℝ)) A.degree weight)
local notation "slots" => previousPeers A S ready digits Z T frm vertex f B wire K traffic weight roster
local notation "hostFields" => peerData (a:=field) A S ready digits Z T frm vertex
local notation "chart" => rotorEntry A S ready digits native Z T frm groupKey vertex
local notation "oldKey" => DescentOrderedReset.grains W A.grainCount order
local notation "book" => T.columns
local notation "R" => Z.placement

local notation "board" => boardFor (field := field) A S ready digits order Z T frm groupKey vertex word rank
local notation "headAt" => base (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "bankV" => fun g : (R).Good=>frm.host.symm g.val.1
local notation "bankH" => fun g : (R).Good=>Z.rootBlock T (.inl g)
local notation "landing" => localAddress («c» := T.commonDepth) A native S ready digits frm.basis


local notation "rr" => DescentRotorWindowArchive.count A.degree L A.cap
local notation "cells" => L*(2*A.cap)
local notation "imageBits" => DescentRotorWindowArchive.output Z.n L A.cap

include room signBits onWire roster in
/-- The prior signed-chip and stencil reads are precisely those of the existing fallback window.
One inverse-GL comparison family and a host-scalar broadcast complete the good rotor's input. -/
theorem issued_rotor {M w : ℕ} (which : Bool) (root : ℕ×ℕ)
    (tables : Fin rr→Tables) (reads : Fin rr→Expr) (menu : DescentSIMDLookup.Banks) (mid out : ℕ) (mem : Memory w)
    (xs : Fin H→Block c→DescentRotorWindowArchive.RowData A.degree L A.cap field)
    (actual : ∀v hi,xs (vertex v) hi=board v hi)
    (saw : ∀j : DescentRotorWindowArchive.Input A.degree L A.cap,
      Source (reads (DescentRotorWindowArchive.ix j)) (fun a g=>xs a g j) M mem)
    (pos : 0<M) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M (mem:Memory w))
    (roomMem : mid+H*chunks (2^c) M<2^w)
    (fits : DescentSIMDLookup.Fits menu (field*rr) imageBits M H (2^c) w out)
    (rom : resident (DescentRotorWindowArchive.law («D»:=A.degree) («L»:=L) (cap:=A.cap) (field:=field) remain Z.n which root)
      menu H (2^c) M mem)
    (dictLow : menu.dictionary.base+2^((field*rr)*M)≤ mid) (maskLow : menu.mask.base+H*chunks (2^c) M≤ mid)
    (link : menu.source.base=mid) (chron : DonorOrder A digits) (sorted : SourceSorted W order)
    (tickets : (R).OrderedTickets oldKey) (wide : max (max remain Y) (2^remain)<2^field) (nWide : Z.n<field) :
    let act:=assembly tables reads
    let rows:=H*chunks (2^c) M
    let dst:=imageBank H (2^c) M out menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H (2^c) M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀g' : (R).Good,(Z.goodLabel T g').val=root→∀i j:Fin Y,
      DescentPackedResetRotorRoles.matrix Z.n (DescentPackedRotorMatrix.bins cells)
        ((digit imageBits (lane (bankH g') pos).val (dst (out+(row H (2^c) M
          (position (vertex (bankV g')) (bankH g') pos)).val)).val:ℕ):Cell imageBits) i j=
        DescentBaseProfile.matrixOfBundles (DescentChosenRouter.source (R) which g') (DescentChosenRouter.target (R) which g') i j) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,read,frame⟩:=DescentRotorWindowArchive.gathered (r:=remain) (n:=Z.n) which root tables reads menu mid out xs pos mem
    bounds constants saw roomMem fits rom dictLow maskLow link
  refine ⟨run,?_,frame⟩
  intro g' located i j
  have observed:=read (vertex (bankV g')) (bankH g')
  rw [actual,←located] at observed
  have castCell (v : Cell imageBits) : ((v.val : ℕ) : Cell imageBits) = v :=
    Fin.ext (Fin.val_cast_of_lt v.isLt)
  rw [observed]
  let value : Cell imageBits := DescentRotorWindowArchive.matrix remain Z.n which
    (Z.goodLabel T g').val (board (bankV g') (bankH g'))
  refine (congrArg (fun z : Cell imageBits =>
    DescentPackedResetRotorRoles.matrix Z.n (DescentPackedRotorMatrix.bins cells) z i j) (castCell value)).trans ?_
  exact installed_matrix A S ready digits order Z T frm groupKey vertex word rank room signBits onWire
    f B wire K traffic weight roster chron sorted tickets wide nWide which g' i j

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
