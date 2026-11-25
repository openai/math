import OAI.Hierarchy.DescentFallbackWindowGeometry
import OAI.Hierarchy.DescentResetSignedStencilRun

namespace OAI
/-! # The occupied mixed-device key from the selected GL and the shared measured chart -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentStageEdgeReceipt DescentFallbackShapeTable DescentRosterOrder DescentResetHostSize
open DescentPackedLeafSelector DescentPlainTerminal DescentPlainTerminal.Suffix DescentFallbackRankRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "Y" => 2^Z.n
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "here" => donor digits frm.basis fit
local notation "ord" => frm.host.symm.toEmbedding.trans vertex
local notation "amountFit" => (2^Ht:ℕ)
local notation "Δ" => A.degree
local notation "short" => fun t : Z.Fallback=>shortName c (T.code t)
local notation "shape" => chartShape A S ready Z T
local notation "hostAt" => fun t : Z.Fallback=>frm.host.symm (Prod.fst (T.code t))
local notation "rootAt" => selectedRoot A S ready Z T
local notation "arr" => leafPanel A S ready digits native Z T frm
variable (n f B wire K : ℕ) (wt : V→Block m→ℕ) (flow : V→V→Block m→ℝ)
variable (roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (vertex.trans Fin.valEmbedding) A.near n f B wire K flow A.degree wt)
variable (bank : DescentSharedBookScan.Chart) (source : Memory w) (target : ℕ)
variable (header : fixed bank (Z.k-T.commonDepth) (2^Z.n) A.degree H source)
    (safe : Room bank (Z.k-T.commonDepth) (2^Z.n) A.degree H w target)
variable (table : DescentNativeFallbackShapes.Stored bank.shapes (Z.k-T.commonDepth) (32*Nat.clog 2 (2*A.degree)) g f
    (2^Z.n) (2^Ht) source)
variable (old : ∀ (u : V) (j : Fin A.degree),source (bank.neighbors.base+((vertex u).val*A.degree+j.val))=
    (hostDigit vertex (hostRoster A (vertex.trans Fin.valEmbedding) u j):Word w))
variable (hub : ∀u,source (bank.isHub.base+(vertex u).val)=((A.hub u).toNat:Word w))
variable (ww : 0<w) (bitsFit : Ht+2≤w)
variable (avail : ∀t : Z.Fallback,∀i z,z∈DescentFallbackLeafScan.localShape (Z.k-T.commonDepth)
    (32*Nat.clog 2 (2*A.degree)) g f (shortName T.commonDepth (T.code t)).2 i→shapeNumber z+1<2^w)
variable (encoded : ∀t : Z.Fallback,shapeNumber (shortName T.commonDepth (T.code t)).2<2^w)
local notation "rank" => ranks (a:=r) («Y»:=Y) («D»:=Δ) bank amountFit (Ht+2) source
variable (word : Host J V k→ℕ) (room : ∀u,word u+1<2^field)
variable (onWire : ∀s (e : Grain A),word (home A (endSite A s e))=
    peerShapeWord A S ready digits Z T frm s (home A (endSite A s e)))
variable (signBits : DescentSignedCableCodec.width A.degree A.cap≤field) (countBits : Ht+2≤field)
local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank
variable (allSites : ∀ (v : V) (hi : Block T.commonDepth) (lo : Fin (2^(m-T.commonDepth))),
    word (donor digits frm.basis (frm.enough.trans (Nat.sub_le ..)) v hi lo)/2 =
      Stencil.shapeCode (m-T.commonDepth) (2^Z.n) (fieldsRelative T.commonDepth
        (DescentPlainTerminal.endpoint A.near (fun u => Z.placement.b (frm.host u))
          frm.basis wt f (32*Nat.clog 2 (2*A.degree)) B g (2^Z.n) roster.2.2.2.2.2.choose
          (fun u j => (frm.host u,j) ∈ Z.placement.keys) A.hub v
          ((rearrange frm.basis).symm (join (frm.enough.trans (Nat.sub_le ..)) hi lo)))))

include roster safe header table old hub ww bitsFit avail encoded allSites room onWire signBits countBits in
theorem fallback_key (s : Bool) (t : Z.Fallback) :
    DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s (Z.fallLabel T t,(T.code t).2.2)
      (win (hostAt t) (rootAt t))=Z.fallbackKey T s t (arr s t) := by
  let ticket:=(Z.fallLabel T t,(T.code t).2.2)
  let raw:=win (hostAt t) (rootAt t)
  let center:=shape t
  have capRoom : DescentFallbackPeriod.rootCell r Z.n ticket<rows r Y:=center.isLt
  have found:=(frm.measured_presence ids A.near n f B wire K Δ wt flow roster (hostAt t) (rootAt t) ticket
    (fun j=>word (here (hostAt t) (rootAt t) j)) (allSites _ _)).mp ⟨t,(frm.host.apply_symm_apply _).symm,rfl,rfl⟩
  have occupied : ∃j,DescentFallbackPeriod.localWord raw j/2=DescentFallbackPeriod.rootCell r Z.n ticket := by
    obtain ⟨j,hj⟩:=found
    exact ⟨j,(congrArg (·/2) (window_own A S ready digits native Z T frm groupKey vertex word rank room _ _ _)).trans hj⟩
  have amountRead:=measured_amount A S ready digits Z T frm vertex
    n f B wire K wt flow roster bank source target header safe table old hub ww bitsFit avail s t
  change (choose _ (DescentSharedBookScan.ticket (center,0,center)) _).val=_ at amountRead
  rw [choose_ticket] at amountRead
  have cost : DescentFallbackPeriod.score raw (center,0,center)=(T.leaves.window (short t)).card :=
    (window_rank A S ready digits native Z T frm groupKey vertex word rank countBits _ _ _).trans amountRead
  have levels : Nat.clog 2 (T.leaves.window (short t)).card=(Z.placement.fallbackBook s t).height :=
    (T.leaves.depth s t).symm
  rw [DescentFallbackPeriod.present s ticket raw occupied capRoom]
  change some (Sum.inr (_,_,DescentPackedFallbackTree.pack Ht
    (Nat.clog 2 (DescentFallbackPeriod.score raw (center,0,center))) _))=_
  rw [cost,levels]
  apply congrArg (fun p=>some (Sum.inr (DescentResetCableSlots.interval r ticket.1,
    DescentResetCableSlots.optional ticket.2,DescentPackedFallbackTree.pack Ht _ p)))
  funext j
  obtain ⟨⟨lo,z⟩,rfl⟩:=finProdFinEquiv.surjective j
  simp only [Equiv.symm_apply_apply]
  change pick Ht (DescentFallbackPeriod.score raw (center,0,center)) _ = _
  rw [cost]
  apply window_slot A S ready digits native Z T frm groupKey vertex word rank room signBits onWire countBits s t lo z
  have prior := measured_before A S ready digits native Z T frm groupKey vertex
    n f B wire K wt flow roster bank source target header safe table old hub ww bitsFit avail encoded s t (finProdFinEquiv (lo,z))
  simpa only [Equiv.symm_apply_apply, shortName] using prior

include roster room allSites in
theorem fallback_ghost (s : Bool) (p : Code r×Option (Fin Y)) (v : V) (hi : Block c)
    (absent : Z.atRoot T ord (vertex v,hi,.inr p)=none) :
    DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s p (win v hi)=none := by
  apply DescentFallbackPeriod.absent
  intro lo same
  have present:=(frm.measured_presence ids A.near n f B wire K Δ wt flow roster v hi p
    (fun j=>word (here v hi j)) (allSites _ _)).mpr ⟨lo,by
      rw [←window_own A S ready digits native Z T frm groupKey vertex word rank room v hi lo];exact same⟩
  obtain ⟨t,vEq,jEq,kind⟩:=present
  apply (Z.empty_at T ord _).mp absent (.inr t)
  change (vertex (frm.host.symm (T.code t).1),Z.rootBlock T (.inr t),Z.rootTicket T (.inr t))=_
  rw [vEq,Equiv.symm_apply_apply,jEq,kind]

section Received
variable {rawWords : Fin H→Block T.commonDepth→Fin (2^(m-T.commonDepth))→ℕ} {peers : Fin H→Fin A.degree→Option (Fin H)}
    {marks : Fin H→Block T.commonDepth→Fin (2^(m-T.commonDepth))→Fin (2*A.cap)→Option (Live A.degree A.cap)}
variable (ownCell : ∀v hi i,rawWords (vertex v) hi i=word (donor digits frm.basis (frm.enough.trans (Nat.sub_le ..)) v hi i))
variable (neighbors : ∀v j,peers (vertex v) j=(hostRoster A (vertex.trans Fin.valEmbedding) v j).map vertex)
variable (wireCells : ∀v hi i j,marks (vertex v) hi i j=
    signedPanel A native S ready (cableNames k (groupRank groupKey (vertex.trans Fin.valEmbedding)))
      (donor digits frm.basis (frm.enough.trans (Nat.sub_le ..)) v hi i) j)
set_option quotPrecheck false in
local notation "observed" => DescentFallbackPeriod.inputs (field:=field) rawWords peers marks (fun u j=>(rank u j).val)

include ownCell neighbors wireCells roster safe header table old hub ww bitsFit avail encoded allSites room onWire signBits countBits in
/-- Both the selected root and every absent candidate are classified by the packet
actually gathered at the original, potentially padded, rectangle. -/
theorem received_fallback_key (s : Bool) (t : Z.Fallback) :
    DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s (Z.fallLabel T t,(T.code t).2.2)
       (observed (vertex (hostAt t)) (rootAt t))=Z.fallbackKey T s t (arr s t) := by
  rw [window_input A S ready digits native Z T frm groupKey vertex word rank ownCell neighbors wireCells]
  apply fallback_key (roster:=roster) (bank:=bank) (source:=source) (target:=target) <;> assumption

include ownCell neighbors wireCells roster room allSites in
theorem received_fallback_ghost (s : Bool) (p : Code r×Option (Fin Y)) (v : V) (hi : Block c)
    (absent : Z.atRoot T ord (vertex v,hi,.inr p)=none) :
    DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s p (observed (vertex v) hi)=none := by
  rw [window_input A S ready digits native Z T frm groupKey vertex word rank ownCell neighbors wireCells]
  apply fallback_ghost (roster:=roster) (word:=word) (v:=v) (hi:=hi) <;> assumption

end Received
end
end Hierarchy.DescentSixParty.GroupStage

end OAI
