import OAI.Hierarchy.DescentSignedChartAddress

namespace OAI
/-! # The native previous-host score returned for a concrete old signed slot -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentRosterOrder
open DescentFallbackRankRAM DescentFallbackShapeTable
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank groupKey ids)
local notation "bookSize" => 2^Z.n
local notation "r" => Z.k-T.commonDepth
local notation "cap" => (2^Ht:ℕ)
local notation "bookDegree" => A.degree
local notation "bookDepth" => 32*Nat.clog 2 (2*bookDegree)
local notation "points" => Fin (2^(m-T.commonDepth)*(2*A.cap))
local notation "term" => fallbackCell A S ready digits Z T frame
local notation "short" => fun t : Z.Fallback=>shortName T.commonDepth (T.code t)
local notation "shape" => chartShape A S ready Z T
local notation "ticketAt" => chartTicket A S ready digits native Z T frame groupKey vertex
local notation "arrive" => chartArrival A S ready native groupKey vertex
local notation "actual" => signedPeer A native S ready names
local notation "chart" => hostRoster A ids
variable (n f B wire K : ℕ) (wt : V→Block m→ℕ) (flow : V→V→Block m→ℝ)
variable (roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g frame (vertex.trans Fin.valEmbedding) A.near n f B wire K flow A.degree wt)
variable (bank : DescentSharedBookScan.Chart) (mem : Memory w) (out : ℕ)
variable (header : fixed bank (Z.k-T.commonDepth) (2^Z.n) A.degree H mem) (room : Room bank (Z.k-T.commonDepth) (2^Z.n) A.degree H w out)
variable (tables : DescentNativeFallbackShapes.Stored bank.shapes (Z.k-T.commonDepth) (32*Nat.clog 2 (2*A.degree)) g f (2^Z.n) (2^Ht) mem)
variable (old : ∀ (u : V) (j : Fin A.degree),mem (bank.neighbors.base+((vertex u).val*A.degree+j.val))=(hostDigit vertex ((hostRoster A (vertex.trans Fin.valEmbedding)) u j):Word w))
variable (hubs : ∀u : V,mem (bank.isHub.base+(vertex u).val)=((A.hub u).toNat:Word w))
variable (ww : 0<w) (bitsFit : Ht+2≤w)
variable (avail : ∀t : Z.Fallback,∀i z,z∈DescentFallbackLeafScan.localShape (Z.k-T.commonDepth) (32*Nat.clog 2 (2*A.degree)) g f (shortName T.commonDepth (T.code t)).2 i→shapeNumber z+1<2^w)
variable (encFits : ∀t : Z.Fallback,shapeNumber (shortName T.commonDepth (T.code t)).2<2^w)
local notation "origin" => fun t : Z.Fallback=>frame.host.symm (Prod.fst (short t))
local notation "scores" => fun t : Z.Fallback=>DescentSharedBookScan.ranks (a:=r) (Y:=bookSize) (D:=bookDegree) bank cap (Ht+2) mem (vertex (origin t))
local notation "rankAt" => leafRankAt A S ready Z T

include roster header room tables old hubs ww bitsFit avail in
theorem measured_amount (s : Bool) (t : Z.Fallback) :
    (choose (width r bookSize bookDegree) (amount (Δ:=bookDegree) (shape t)) (DescentSIMDLookup.encode (Ht+2) _ (scores t))).val=
      (T.leaves.window (short t)).card := by
  let p : Fields r bookSize bookDegree :=(shape t,0,shape t)
  have read:=frame.shared_book_total vertex A.near n f B wire K bookDegree wt flow roster chart
    (hostRoster_mem A ids) t bank mem out p header room tables old hubs ww (chartShape_read A S ready Z T t) (avail t) rfl
  change (choose _ (ticket p) (DescentSIMDLookup.encode (Ht+2) _ (scores t))).val=_
  rw [choose_ticket]
  exact rank_eq_of_raw bank cap (Ht+2) out mem (vertex (origin t)) p _
    read (leafAmount_fit A S ready Z T s t) bitsFit

include roster header room tables old hubs ww bitsFit avail encFits in
theorem measured_before (s : Bool) (t : Z.Fallback) (id : points) :
    let loc:=finProdFinEquiv.symm id
    let u:=oldCellAt A S ready digits Z T frame t loc.1
    (choose (width r bookSize bookDegree) (ticketAt s t u loc.2) (DescentSIMDLookup.encode (Ht+2) _ (scores t))).val=
      (signedFields A S ready digits native Z T frame names s t id).before := by
  obtain ⟨⟨lo,q⟩,rfl⟩:=finProdFinEquiv.surjective id
  let u:=oldCellAt A S ready digits Z T frame t lo
  simp only [signedFields,Equiv.symm_apply_apply]
  change (choose _ (ticketAt s t u q) (DescentSIMDLookup.encode (Ht+2) _ (scores t))).val =
    (actual s u q).elim 0 (fun b => rankAt (short t) (short (term (!s) b)))
  rw [chartTicket_read]
  have truePeer:=chartArrival_peer A S ready native groupKey vertex s u q
  cases addr:arrive s u q with
  | none=>
    have gone : actual s u q=none:=truePeer.symm.trans (by rw [addr];rfl)
    simp only [gone, Option.elim_none, choose_empty, Fin.val_zero]
  | some z=>
    rcases z with ⟨j,b⟩
    have remote : actual s u q=some b:=truePeer.symm.trans (by rw [addr];rfl)
    have recv:=chartArrival_host A S ready digits native Z T frame groupKey vertex s u q j b addr
    let dest:=term (!s) b
    let p : Fields r bookSize bookDegree :=(shape t,j.succ,shape dest)
    have read:=frame.shared_book_prefix vertex A.near n f B wire K bookDegree wt flow roster chart
      (hostRoster_mem A ids) t bank mem out p header room tables old hubs ww
      (chartShape_read A S ready Z T t) (avail t) j b.1.2 recv.1 rfl
      (by rw [show decode r bookSize p.2.2.val=(short dest).2 from chartShape_read A S ready Z T dest];exact encFits dest)
    have dst : (frame.host b.1.2,decode r bookSize p.2.2.val)=short dest :=
      Prod.ext recv.2.symm (chartShape_read A S ready Z T dest)
    dsimp only at read
    rw [dst] at read
    have bound:=(leafRankAt_le A S ready Z T (short t) (short dest)).trans_lt (leafAmount_fit A S ready Z T s t)
    have scored:=rank_eq_of_raw bank cap (Ht+2) out mem (vertex (origin t)) p
      (rankAt (short t) (short dest)) read bound bitsFit
    simp only [remote, Option.elim_some]
    change (choose _ (ticket p) (DescentSIMDLookup.encode (Ht+2) _ (scores t))).val=_
    rw [choose_ticket]
    exact scored

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
