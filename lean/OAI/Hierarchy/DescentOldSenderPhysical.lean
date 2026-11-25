import OAI.Hierarchy.DescentOldContactSender

namespace OAI
/-! # The previous signed donor emits precisely its installed contact joint and book height -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open DescentRotorWindowScore DescentPackedTicketChronology DescentPacking
open DescentRotorWindowArchive DescentCanonicalPorts DescentOldContactSender DescentContactSenderTicket
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
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank groupKey ids)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
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
variable (word : Host J V k→ℕ) (rank : Fin H→Fin (width (Z.k-T.commonDepth) (2^Z.n) A.degree)→Cell (Ht+2))


local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank
local notation "use" => useRotor Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old
local notation "endAt" => DescentIssuedFallbackPanel.endSite A
variable (room : ∀u,word u+1<2^field) (signBits : DescentSignedCableCodec.width A.degree A.cap≤field)
variable (onWire : ∀s : Bool, ∀e : Grain A,
  word (home A (DescentIssuedFallbackPanel.endSite A s e))=
    peerShapeWord A S ready digits Z T frm s (home A (DescentIssuedFallbackPanel.endSite A s e)))




variable (f B wire K : ℕ) (traffic : V→V→Block m→ℕ) (weight : V→Block m→ℕ)
variable (roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (vertex.trans Fin.valEmbedding) A.near Z.n f B wire K (fun v z i=>(traffic v z i:ℝ)) A.degree weight)
local notation "slots" => previousPeers A S ready digits Z T frm vertex f B wire K traffic weight roster
local notation "hostFields" => peerData (a:=field) A S ready digits Z T frm vertex
local notation "chart" => rotorEntry A S ready digits native Z T frm groupKey vertex
local notation "oldKey" => DescentOrderedReset.grains W A.grainCount order
local notation "book" => T.columns
local notation "R" => Z.placement

local notation "board" => boardFor (field:=field) A S ready digits order Z T frm groupKey vertex word rank
local notation "sample" => fun v hi=>withRank (board v hi) (win v hi)
local notation "wireAt" => fun s e=>wireWord s (home A (endAt s e))
local notation "ticket" => fun s e=>Z.senderJoint T s ((R).contact e)
local notation "baseOf" => base (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "nearPort" => fun s e=>(cableChip A S ready native groupKey vertex s e).neighbor

theorem sender_window (v : V) (hi : Block c) : window (sample v hi)=win v hi := window_observed ..

include room signBits in
theorem sender_vacant (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap))
    (empty : atSlot A native S ready s (here v hi j) z=none) :
    point Ht s (sample v hi) (j,z)=fun _=>0 := by
  apply DescentOldContactSender.blank
  rw [sender_window,window_arrival A S ready digits native Z T frm groupKey vertex word rank room signBits]
  have a:=chartArrival_peer A S ready native groupKey vertex s (here v hi j) z
  rw [signedPeer_slot,empty,Option.map_none] at a
  rw [Option.map_eq_none_iff.mp a]
  rfl

variable (law : DonorOrder A digits) (sorted : SourceSorted W order) (tickets : Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order))
    (wide : max (max (Z.k-T.commonDepth) (2^Z.n)) (2^(Z.k-T.commonDepth))<2^field) (nWide : Z.n<field)
local notation "arr" => leafPanel A S ready digits native Z T frm

/- This is the selected fallback-key read of the actual measured chart at its own root. It
is supplied directly by `GroupStage.fallback_key` on the same signed window. -/
variable (books : ∀s t,DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s
  (Z.fallLabel T t,(T.code t).2.2) (fallbackWindow (field:=field) A S ready digits (order.trans Fin.valEmbedding) Z T frm groupKey vertex word rank
    (frm.host.symm (T.code t).1) (selectedRoot A S ready Z T t))=
    Z.fallbackKey T s t (leafPanel A S ready digits (order.trans Fin.valEmbedding) Z T frm s t))

include room signBits onWire law sorted tickets wide nWide roster books in
theorem sender_at (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap)) (e : Grain A)
    (found : atSlot A native S ready s (here v hi j) z=some e) :
    point Ht s (sample v hi) (j,z) = ![ticket s e,Z.contactDepth s ((R).contact e),(nearPort s e).val] := by
  let chip:=nearPort s e
  let far:=wireAt (!s) e
  let localWordValue:=wireAt s e
  have addr:=(atSlot_iff A native S ready s _ z e).mp found
  have actual : here v hi j=home A (endAt s e):=(congrArg Prod.fst addr).symm.trans (port_fst A s e)
  have arrived : DescentFallbackPeriod.arrival (window (sample v hi)) s j z=some (chip,far) := by
    rw [sender_window,window_arrival A S ready digits native Z T frm groupKey vertex word rank room signBits,
      arrival_at A S ready native groupKey vertex s e _ z found,Option.map_some]
    exact congrArg (fun y=>some (chip,y)) (onWire (!s) e)
  have localAt : DescentFallbackPeriod.localWord (window (sample v hi)) j=localWordValue := by
    rw [sender_window,window_own A S ready digits native Z T frm groupKey vertex word rank room,actual,onWire s e]
  let sensor : Fin 3→Cell field := ![1,localWordValue,far]
  have live : (sensor 0).val≠0 := by
    have one : 1<2^field:=one_lt_pow₀ (by decide) (Nat.zero_lt_of_lt nWide).ne'
    change 1 % (2^field) ≠ 0
    rw [Nat.mod_eq_of_lt one]
    decide
  have prior (w : Bool) : wireAt w e<2^field :=
    (onWire w e).symm.trans_lt (Nat.lt_of_succ_lt (room _))
  have mine : (sensor 1).val=localWordValue:=Fin.val_cast_of_lt (prior s)
  have theirs : (sensor 2).val=far:=Fin.val_cast_of_lt (prior (!s))
  by_cases good : use e
  · let p : {p : Grain A // use p}:=⟨e,good⟩
    let tag:=Z.goodLabel T (baseOf p s)
    have hc : (R).contact e=.inl ((R).ticket p):=by
      simp only [Placement.contact,DescentChosenRouter.contact,dite_eq_left good]
      rfl
    have seen : DescentRotorWindowScore.entry (window (sample v hi)) s (j,z)=some (chart s e):=by
      rw [sender_window]
      have installed := entry_physical A S ready digits native Z T frm groupKey vertex word rank
        room signBits onWire s v hi j z e found
      change DescentRotorWindowScore.entry (win v hi) s (j,z) = if use e then some (chart s e) else none at installed
      exact installed.trans (ite_eq_left good)
    have chosen:=DescentOldContactSender.choice_read localWordValue far (.inl tag) sensor live mine theirs
      (paid_stencil_root A S ready digits Z T frm s p sensor live mine theirs)
    rw [←localAt] at chosen
    have col:=column_here A S ready digits order Z T frm groupKey vertex word rank room signBits onWire f B wire K
      traffic weight roster law sorted tickets s v hi j z p found wide nWide
    have out:=DescentOldContactSender.paid (Ht:=Ht) s (sample v hi) (j,z) chip far tag (chart s e)
      ((R).outputName c s ((R).ticket p)).2 arrived chosen seen (col.trans (T.columns.read s ((R).ticket p)).symm)
    rw [out]
    change _ = ![Z.senderJoint T s ((R).contact e),Z.contactDepth s ((R).contact e),chip.val]
    rw [hc]
    change _ = ![ (DescentResetLocalRoster.rootId r Y (.inl (Z.goodLabel T ((R).ends s ((R).ticket p).1)))).val*(Y+2^Ht)+
      ((R).outputName c s ((R).ticket p)).2.val+1,0,chip.val]
    rw [(R).owned p s]
  · obtain ⟨d,hd⟩ : ∃d,(R).contact e=.inr d:=by simp [Placement.contact,DescentChosenRouter.contact,good]
    let t:=fallEnd (R) s d
    have member : falls A S ready Z s t e:=by change (R).owner s ((R).contact e)=_;rw [hd];rfl
    let tag:=(Z.fallLabel T t,(T.code t).2.2)
    have chosen:=DescentOldContactSender.choice_read localWordValue far (.inr tag) sensor live mine theirs
      (fallback_stencil_root A S ready digits Z T frm s e t good member sensor live mine theirs)
    rw [←localAt] at chosen
    have loc:=contact_sender_located A S ready digits native Z T frm s v hi j z e found
    change Z.rootVertex T ((R).owner s ((R).contact e))=frm.host v ∧ Z.rootBlock T ((R).owner s ((R).contact e))=hi at loc
    have memberEq : (R).owner s ((R).contact e)=.inr t := member
    rw [memberEq] at loc
    have atV : hostAt t=v := by change frm.host.symm (Z.rootVertex T (.inr t))=v;rw [loc.1,Equiv.symm_apply_apply]
    have atH : rootAt t=hi:=loc.2
    let tree:=(R).fallbackBook s t
    let link : DescentRouterSlots.LinkId (R).owner s (.inr t):=⟨(R).contact e,member⟩
    let leaf:=tree.codes link
    have installed : treePanel (DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s tag
        (window (sample v hi)))=some (DescentPackedFallbackTree.pack Ht tree.height (arr s t)) := by
      rw [sender_window,←atV,←atH,books]
      rfl
    have fp : fallbackPanel A S ready digits native Z T frm s t (j,z)=some e := by
      change (atSlot A native S ready s (here (hostAt t) (rootAt t) j) z).filter _=_
      rw [atV,atH,found];simp only [Option.filter_some,decide_eq_true_eq]; exact ite_eq_left member
    have arrival : ∃a,arr s t (finProdFinEquiv (j,z))=some a ∧ a.val=DescentTreePrefixIntervals.start Ht leaf := by
      simp only [leafPanel,Equiv.symm_apply_apply,fp,Option.bind_some,arrivedLeaf,dite_eq_left member]
      exact ⟨_,rfl,rfl⟩
    have out:=DescentOldContactSender.exceptional (Ht:=Ht) s (sample v hi) (j,z) chip far tag tree.height leaf
      (T.bookHeight s t) (arr s t) Z.layerBits arrived chosen installed arrival
    rw [out]
    have leg : link=DescentChosenRouter.fallLeg (R) s d :=Subtype.ext hd
    change _ = ![ (DescentResetLocalRoster.rootId r Y (Z.rootTicket T ((R).owner s ((R).contact e)))).val*(Y+2^Ht)+
      Z.contactSlotWord T s ((R).contact e)+1,Z.contactDepth s ((R).contact e),chip.val]
    rw [memberEq,hd]
    change ![_,_,_] = ![ (DescentResetLocalRoster.rootId r Y (.inr tag)).val*(Y+2^Ht)+
      (Y+(DescentRotor.bitWord tree.height (tree.codes (fallLeg (R) s d))).val)+1,tree.height,chip.val]
    rw [←leg]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
