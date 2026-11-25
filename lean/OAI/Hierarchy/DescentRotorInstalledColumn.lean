import OAI.Hierarchy.DescentRotorHostMetadata

namespace OAI
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
local notation "physical" => signedPeer A native S ready names
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

def boardFor (v : V) (hi : Block c) := observed (win v hi) (previousDigit frm.basis fit hi) (hostFields v)
local notation "board" => boardFor (field:=field) A S ready digits order Z T frm groupKey vertex word rank

include room signBits onWire in
theorem ticket_here (law : DonorOrder A digits) (sorted : SourceSorted W order) (tickets : (R).OrderedTickets oldKey)
    (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap)) (p : {e : Grain A // use e})
    (found : atSlot A native S ready s (here v hi j) z=some p.val) :
    ((R).ticket p).2.val=DescentRotorWindowScore.tally (win v hi) s (previousDigit frm.basis fit hi) (j,z)%((R).span ((R).ticket p).1) := by
  have addr:=(atSlot_iff A native S ready s _ z p.val).mp found
  have donorAt:=(port_fst A s p.val).symm.trans (congrArg Prod.fst addr)
  have hostRead : (A.pos (endAt s p.val)).2=v:=congrArg (fun a : old=>a.1.2) donorAt
  have oldDigit:=entered_digit A S ready digits native Z T frm s v hi j z p.val found s
  have highRead : rotorSourceHigh A S ready Z T s p=hi := by
    apply Fin.ext
    change coarseName c (T.code (T.home (endAt s p.val)))=_
    refine (frm.homeHigh (endAt s p.val)).trans ?_
    rw [oldDigit, Equiv.apply_symm_apply]
    exact congrArg Fin.val (DescentPlainTerminal.high_join fit hi j)
  have location : localAddress A native S ready digits frm.basis s p.val=(j,z) := by
    unfold localAddress
    rw [addr]
    refine Prod.ext ?_ rfl
    apply Fin.ext
    simp [subcell,donor,oldBlock,join,Equiv.symm_apply_apply,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  simpa only [hostRead,highRead,location] using counted_ticket A S ready digits order Z T frm groupKey vertex word rank
    room signBits onWire law sorted tickets s p

theorem span_here (s : Bool) (v dest : V) (i : Fin A.degree) (p : {e : Grain A // use e})
    (actual : hs v i=some dest) (own : (A.pos (endAt s p.val)).2=v) (peer : (A.pos (endAt (!s) p.val)).2=dest)
    (wide : Z.n<field) :
    (hostFields v i i 1).val=(R).span ((R).ticket p).1 := by
  have ownName:=rotorHost A S ready digits Z T frm p s
  have peerName:=rotorHost A S ready digits Z T frm p (!s)
  rw [own] at ownName;rw [peer] at peerName
  have room : min (T.columns.size (frm.host v) (frm.host dest)) Y<2^field :=
    (min_le_right ..).trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) wide)
  unfold peerData
  rw [actual]
  change ((min (T.columns.size (frm.host v) (frm.host dest)) Y : Nat) : Cell field).val = _
  rw [Fin.val_cast_of_lt room]
  rw [min_comm,←ownName,←peerName,←(R).owned p s,←(R).owned p (!s)]
  exact DescentReservationHeader.observed_span (T:=T) s _


include room signBits onWire in
/-- All four request fields follow from the actual incoming chip and its local prior-window count. -/
theorem requests_here (law : DonorOrder A digits) (sorted : SourceSorted W order) (tickets : (R).OrderedTickets oldKey)
    (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap)) (p : {e : Grain A // use e})
    (found : atSlot A native S ready s (here v hi j) z=some p.val)
    (wide : max (max remain Y) (2^remain)<2^field) (nWide : Z.n<field) (q : Fin 4) :
    let anchor:=(R).ends s ((R).ticket p).1
    let remote:=(R).ends (!s) ((R).ticket p).1
    let this:=chart s p.val
    let peer:=(cableChip A S ready native groupKey vertex s p.val).neighbor
    (fieldRow (r:=remain) (n:=Z.n) (board v hi) s (j,z) peer this (DescentPackedReservationColumn.request q)).val=
      ![relative (m:=c) (R).b anchor.val.1,(DescentCanonicalPorts.short (m:=c) (R).b anchor.val).2,
        (DescentCanonicalPorts.short (m:=c) (R).b remote.val).2,((R).ticket p).2.val] q := by
  let peer:=(cableChip A S ready native groupKey vertex s p.val).neighbor
  let dest:=(A.pos (endAt (!s) p.val)).2
  have chartFound:=arrival_at A S ready native groupKey vertex s p.val _ z found
  have present:hs v peer=some dest:=(chartArrival_host A S ready digits native Z T frm groupKey vertex s _ _ _ _ chartFound).1
  have oldPair:=(port_fst A s p.val).symm.trans (congrArg Prod.fst ((atSlot_iff A native S ready s _ z p.val).mp found))
  have hostRead : (A.pos (endAt s p.val)).2=v :=congrArg (fun a : old=>a.1.2) oldPair
  have span:=span_here A S ready digits Z T frm vertex s v dest peer p present hostRead rfl nWide
  have count:=ticket_here A S ready digits order Z T frm groupKey vertex word rank room signBits onWire law sorted tickets s v hi j z p found
  have fieldPos:0<field:=Nat.zero_lt_of_lt nWide
  have raw:=observed_tally (win v hi) (previousDigit frm.basis fit hi) (hostFields v) fieldPos s (j,z)
  have rem (u : (R).Good) : (Z.goodLabel T u).val.2<2^remain :=
    (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right ((R).depth _) c))
  have depth (u : (R).Good) : relative (m:=c) (R).b u.val.1≤remain:=Nat.sub_le_sub_right ((R).depth _) c
  have small:=((R).ticket p).2.isLt
  have bound : (R).span ((R).ticket p).1≤Y := by
    rw [←DescentReservationHeader.observed_span (T:=T) s ((R).ticket p).1]
    exact min_le_left _ _
  have divCode (a b : ℕ) (h : b < 2^remain) : (a*2^remain+b)/2^remain = a := by
    rw [Nat.mul_comm a, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt h, Nat.add_zero]
  have depthRoom : remain < 2^field := (le_trans (le_max_left _ _) (le_max_left _ _)).trans_lt wide
  have lowRoom : 2^remain < 2^field := (le_max_right _ _).trans_lt wide
  have ticketRoom : ((R).ticket p).2.val < 2^field :=
    small.trans_le (bound.trans ((le_max_right _ _).trans (le_max_left _ _))) |>.trans wide
  dsimp only
  rw [row_request, (R).owned p s, (R).owned p (!s)]
  simp only [rotorEntry, rotorInterval A S ready digits Z T frm p s, rotorInterval A S ready digits Z T frm p (!s),
    divCode _ _ (rem _), Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (rem _),
    boardFor, raw, metadata, observed]
  fin_cases q
  · exact Fin.val_cast_of_lt ((depth _).trans_lt depthRoom)
  · exact Fin.val_cast_of_lt ((rem _).trans lowRoom)
  · exact Fin.val_cast_of_lt ((rem _).trans lowRoom)
  · change ((DescentRotorWindowScore.tally (win v hi) s (previousDigit frm.basis fit hi) (j,z) %
        (hostFields v peer peer 1).val : ℕ) : Cell field).val = ((R).ticket p).2.val
    rw [span, ←count, Fin.val_cast_of_lt ticketRoom]

private def moveSlot {U : Type} (near : U→Finset U) {u v : U} (moved : u=v) {D : ℕ} (slot : near v↪Fin D) : near u↪Fin D :=
  moved.symm ▸ slot

private theorem moveSlot_at {U : Type} (near : U→Finset U) {u v : U} (moved : u=v) {D : ℕ} (slot : near v↪Fin D)
    (a : near u) : moveSlot near moved slot a=slot ⟨a.val,moved ▸ a.property⟩ := by cases moved;rfl

include room signBits onWire roster in
theorem column_here (law : DonorOrder A digits) (sorted : SourceSorted W order) (tickets : (R).OrderedTickets oldKey)
    (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap)) (p : {e : Grain A // use e})
    (found : atSlot A native S ready s (here v hi j) z=some p.val)
    (wide : max (max remain Y) (2^remain)<2^field) (nWide : Z.n<field) :
    let peerSlot:=(cableChip A S ready native groupKey vertex s p.val).neighbor
    let current:=fieldRow (field:=field) (r:=remain) (n:=Z.n) (board v hi) s (j,z) peerSlot (chart s p.val)
    (DescentPackedReservationColumn.column Z.n A.degree field (2^remain)
      (encode field (DescentPackedReservationColumn.fields A.degree) current)).val=
      (R).reservedColumn c T.columns.host T.columns.near T.columns.size s ((R).ticket p) := by
  let t:=(R).ticket p
  let anchor:=DescentCanonicalPorts.short (m:=c) (R).b ((R).ends s t.1).val
  let remote:=DescentCanonicalPorts.short (m:=c) (R).b ((R).ends (!s) t.1).val
  let dest:=(A.pos (endAt (!s) p.val)).2
  let peerSlot:=(cableChip A S ready native groupKey vertex s p.val).neighbor
  let cells:=fieldRow (field:=field) (r:=remain) (n:=Z.n) (board v hi) s (j,z) peerSlot (chart s p.val)
  have atHere:=(port_fst A s p.val).symm.trans (congrArg Prod.fst ((atSlot_iff A native S ready s _ z p.val).mp found))
  have hostRead : (A.pos (endAt s p.val)).2=v:=congrArg (fun a : old=>a.1.2) atHere
  have ownName : anchor.1=frm.host v:=by
    change ((R).ends s ((R).ticket p).1).val.1=_
    exact (congrArg (fun u : (R).Good => u.val.1) ((R).owned p s)).trans
      ((rotorHost A S ready digits Z T frm p s).trans (congrArg frm.host hostRead))
  have farName : remote.1=frm.host dest:=by
    change ((R).ends (!s) ((R).ticket p).1).val.1=_
    exact (congrArg (fun u : (R).Good => u.val.1) ((R).owned p (!s))).trans
      (rotorHost A S ready digits Z T frm p (!s))
  have arrival:=arrival_at A S ready native groupKey vertex s p.val _ z found
  have used:hs v peerSlot=some dest:=(chartArrival_host A S ready digits native Z T frm groupKey vertex s _ _ _ _ arrival).1
  let landing:=moveSlot T.columns.near ownName (slots v)
  apply DescentPackedReservationColumn.actual (R) c book s t landing cells
  · exact requests_here A S ready digits order Z T frm groupKey vertex word rank room signBits onWire
      law sorted tickets s v hi j z p found wide nWide
  · intro a n
    let b : T.columns.near (frm.host v):=⟨a.val,ownName ▸ a.property⟩
    have read:=peerData_read (a:=field) A S ready digits Z T frm vertex f B wire K traffic weight roster v dest peerSlot used b n wide
    change (cells (DescentPackedReservationColumn.neighbor (landing a) n)).val=_
    rw [show landing a=slots v b from moveSlot_at ..]
    simp only [cells,row_neighbor,boardFor,metadata,observed]
    simpa only [anchor,remote,←ownName,←farName,min_comm] using read
  · intro a absent
    have ghost : ∀b,slots v b≠a := by
      intro b hit
      let x : T.columns.near anchor.1:=⟨b.val,ownName.symm ▸ b.property⟩
      exact absent x ((moveSlot_at T.columns.near ownName (slots v) x).trans hit)
    change (cells (DescentPackedReservationColumn.neighbor a 1)).val=0
    simp only [cells,row_neighbor,boardFor,metadata,observed]
    exact peerData_empty A S ready digits Z T frm vertex f B wire K traffic weight roster v peerSlot a ghost

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
