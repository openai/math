import OAI.Hierarchy.DescentRotorInstalledMatrix
import OAI.Hierarchy.DescentIssuedGoodHeaders
import OAI.Hierarchy.DescentRecordedReservationRead
import OAI.Hierarchy.DescentFallbackGLWindow

namespace OAI
/-! # The ticket digit and measured pair span from the same gathered predecessor rotor window -/
namespace Hierarchy.DescentReservedProbeInputs
open DescentRotorWindowScore DescentRotorWindowArchive DescentSIMDLookup DescentPackedZip DescentIssuedGoodHeaders
open DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n r b H G M w : ℕ}

/-- Field zero is the actual ordered ticket's position in its pair. Field one is that
reservation's measured span, clipped to the installed number of columns. -/
def value (n r : ℕ) (s : Bool) (data : RowData D L cap b) (j : Slot L cap) (f : Fin 2) : Cell b :=
  match entry (n:=n) (r:=r) (DescentRotorWindowArchive.source data) s j with
  | none=>0
  | some a=>
    if valid : a.neighbor<D then
      let peer : Fin D:=⟨a.neighbor,valid⟩
      if f.val=0 then fieldRow (n:=n) (r:=r) data s j peer a (DescentPackedReservationColumn.request 3)
      else metadata data peer peer 1
    else 0

abbrev slots (L cap : ℕ) := (L*(2*cap))*2

def bundle (n r : ℕ) (s : Bool) (data : RowData D L cap b) : Cell (b*slots L cap) :=
  encode b (slots L cap) (fun j=>let p:=finProdFinEquiv.symm j
    value n r s data (finProdFinEquiv.symm p.1) p.2)

theorem bundle_at (n r : ℕ) (s : Bool) (data : RowData D L cap b) (j : Slot L cap) (f : Fin 2) :
    (encode b (slots L cap)).symm (bundle n r s data) (finProdFinEquiv (finProdFinEquiv j,f))=
      value n r s data j f := by simp only [bundle, Equiv.symm_apply_apply]

/-- A single gathered previous window supplies every donor and both fields. -/
theorem publish (n r : ℕ) (s : Bool)
    (tables : Fin (count D L cap)→Tables) (reads : Fin (count D L cap)→Expr)
    (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (xs : Fin H→Fin G→RowData D L cap b) (positive : 0<M) (mem : Memory w)
    (bounds : Bounds (w:=w) (d:=b) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=b) j) M mem)
    (inputs : ∀j,Source (reads (ix j)) (fun h g=>xs h g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (b*count D L cap) (b*slots L cap) M H G w out.base)
    (rom : resident ((fun data=>bundle n r s (D:=D) (L:=L) (cap:=cap) (b:=b) (fun j=>data (ix j)))
      ∘ (encode b (count D L cap)).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((b*count D L cap)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (extent : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    DescentPackedColony.Reads out (fun h g=>bundle n r s (xs h g)) M dst ∧
    Source (.lookup out .row) (fun h g=>bundle n r s (xs h g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  let emit:=fun data:Fin (count D L cap)→Cell b=>bundle n r s (D:=D) (L:=L) (cap:=cap) (fun j=>data (ix j))
  have src (j : Fin (count D L cap)) : Source (reads j) (fun h g=>xs h g (ix.symm j)) M mem:=by
    simpa using inputs (ix.symm j)
  obtain ⟨run,got,_,frame⟩:=gathered_words emit tables reads menu mid out.base
    (fun h g j=>xs h g (ix.symm j)) positive mem bounds constants src room fit rom dictLow maskLow wire
  have raw : DescentPackedColony.Reads out (fun h g=>bundle n r s (xs h g)) M
      (imageBank H G M out.base menu (image mid (H*chunks G M) (assembly tables reads) mem)) := by
    intro p
    simpa only [emit, Equiv.symm_apply_apply] using got p
  exact ⟨run,raw,source_column out ceiling outputOK _ _ extent raw,frame⟩

/-- Direct Expr reads for either scalar field of each original signed position, reusing the
persistently gathered board on the same memory. -/
theorem projected (n r : ℕ) (s : Bool) (j : Slot L cap) (f : Fin 2)
    (banks : DescentSIMDLookup.Banks) (out : ℕ) (xs : Fin H→Fin G→RowData D L cap b) (m : Memory w)
    (safe : DescentSIMDLookup.Fits banks (b*slots L cap) b M H G w out)
    (arr : DescentPackedColony.Reads banks.source (fun h g=>bundle n r s (xs h g)) M m)
    (dict : resident (DescentFallbackPeriod.project (field:=b) (bytes:=b)
      (finProdFinEquiv (finProdFinEquiv j,f)) 0) banks H G M m) :
    Source (DescentSIMDLookup.lookup banks) (fun h g=>value n r s (xs h g) j f) M m := by
  let digits:=fun h g i=>let p:=finProdFinEquiv.symm (i : Fin (slots L cap))
    value n r s (xs h g) (finProdFinEquiv.symm p.1) p.2
  have issued:=DescentFallbackPeriod.projected banks out (finProdFinEquiv (finProdFinEquiv j,f)) 0 digits m safe arr dict
  simp only [digits, Equiv.symm_apply_apply] at issued
  simpa using issued

end
end Hierarchy.DescentReservedProbeInputs

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open DescentRotorWindowScore DescentPackedTicketChronology DescentPacking
open DescentRotorWindowArchive DescentCanonicalPorts
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




local notation "chart" => rotorEntry A S ready digits native Z T frm groupKey vertex
local notation "oldKey" => DescentOrderedReset.grains W A.grainCount order
local notation "book" => T.columns
local notation "R" => Z.placement

open DescentReservedProbeInputs
local notation "board" => boardFor (field:=field) A S ready digits order Z T frm groupKey vertex word rank

include room signBits onWire in
theorem reserved_probe_inputs (law : DonorOrder A digits) (sorted : SourceSorted W order) (tickets : (R).OrderedTickets oldKey)
    (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap)) (p : {e : Grain A // use e})
    (found : atSlot A native S ready s (here v hi j) z=some p.val)
    (wide : max (max remain Y) (2^remain)<2^field) (nWide : Z.n<field) :
    (value Z.n remain s (board v hi) (j,z) 0).val=((R).ticket p).2.val ∧
    (value Z.n remain s (board v hi) (j,z) 1).val=(R).span ((R).ticket p).1 := by
  let peer:=(cableChip A S ready native groupKey vertex s p.val).neighbor
  let dest:=(A.pos (endAt (!s) p.val)).2
  have physicalRead:=entry_physical A S ready digits native Z T frm groupKey vertex word rank room signBits onWire s v hi j z p.val found
  change entry (win v hi) s (j,z)=if use p.val then some (chart s p.val) else none at physicalRead
  rw [ite_eq_left p.property] at physicalRead
  have read : entry (n:=Z.n) (r:=remain) (DescentRotorWindowArchive.source (board v hi)) s (j,z)=some (chart s p.val):=physicalRead
  have inside : (chart s p.val).neighbor<A.degree:=peer.isLt
  have ask:=requests_here A S ready digits order Z T frm groupKey vertex word rank room signBits onWire
    law sorted tickets s v hi j z p found wide nWide 3
  have chartFound:=arrival_at A S ready native groupKey vertex s p.val _ z found
  have present:hs v peer=some dest:=(chartArrival_host A S ready digits native Z T frm groupKey vertex s _ _ _ _ chartFound).1
  have oldPair:=(port_fst A s p.val).symm.trans (congrArg Prod.fst ((atSlot_iff A native S ready s _ z p.val).mp found))
  have hostRead : (A.pos (endAt s p.val)).2=v:=congrArg (fun a : old=>a.1.2) oldPair
  have actualSpan:=span_here A S ready digits Z T frm vertex s v dest peer p present hostRead rfl nWide
  simp only [DescentReservedProbeInputs.value, read, dite_eq_left inside]
  exact ⟨ask,actualSpan⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
