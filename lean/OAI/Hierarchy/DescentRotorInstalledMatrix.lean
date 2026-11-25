import OAI.Hierarchy.DescentRotorInstalledColumn

namespace OAI
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open DescentRotorWindowScore DescentPackedTicketChronology DescentPacking
open DescentRotorWindowArchive DescentCanonicalPorts
open DescentPackedRotorMatrix DescentResetTrunks DescentPackedResetRotorRoles
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

theorem rotor_owned (s : Bool) (p : {e : Grain A // use e}) :
    (R).owner s ((R).contact p.val)=.inl (headAt p s) := by
  simp [Placement.owner,Placement.contact,DescentChosenRouter.owner,DescentChosenRouter.contact,p.property,(R).owned]
  rfl

theorem rotorCellsAt (s : Bool) (g' : (R).Good) (e : Grain A) (member : (R).owner s ((R).contact e)=.inl g') :
    (A.pos (endAt s e)).2=bankV g' ∧
      group c (rearrange frm.basis (oldBlock digits (home A (endAt s e))))=(bankH g').val := by
  let x : Cells (R) s g':=⟨e,member⟩
  let p : {e : Grain A // use e}:=⟨e,paid (R) s g' x⟩
  have anchor : headAt p s=g':=Sum.inl.inj ((rotor_owned A S ready Z s p).symm.trans member)
  constructor
  · apply frm.host.injective
    rw [frm.host.apply_symm_apply,←anchor,rotorHost A S ready digits Z T frm]
  · change group c (rearrange frm.basis (StarKeys.filled W.graph A.pos A.block digits (endAt s p.val)))=coarse (m:=c) (R).b g'.val
    rw [←anchor,rotorHigh A S ready digits Z T frm]

def physicalRoster (s : Bool) (g' : (R).Good) : Roster (R) s g' (L*(2*A.cap)) where
  index:=⟨fun e=>finProdFinEquiv (landing s e.val),by
    intro e t eqn
    let yes:=fun x : Grain A=>(R).owner s ((R).contact x)=.inl g'
    let this:=panel A native S ready digits frm.basis fit s (bankV g') (bankH g') yes
    have atSite:=rotorCellsAt A S ready digits Z T frm s g'
    have one:=panel_at A native S ready digits frm.basis fit s (bankV g') (bankH g') yes atSite e.val e.property
    have two:=panel_at A native S ready digits frm.basis fit s (bankV g') (bankH g') yes atSite t.val t.property
    rw [finProdFinEquiv.injective eqn] at one
    exact Subtype.ext (Option.some.inj (one.symm.trans two))⟩

include room signBits onWire in
private theorem chart_here (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap))
    (x : Grain A) (found : atSlot A native S ready s (here v hi j) z=some x) :
    let i:=(cableChip A S ready native groupKey vertex s x).neighbor
    DescentFallbackPeriod.arrival (win v hi) s j z=some (i,wireWord (!s) (home A (endAt (!s) x))) ∧
      DescentFallbackPeriod.localWord (win v hi) j=wireWord s (home A (endAt s x)) := by
  have ok:=arrival_at A S ready native groupKey vertex s x _ z found
  have a:=window_arrival A S ready digits native Z T frm groupKey vertex word rank room signBits v hi j z s
  have b:=window_own A S ready digits native Z T frm groupKey vertex word rank room v hi j
  have host : home A (endAt s x)=here v hi j :=
    (port_fst A s x).symm.trans (congrArg Prod.fst ((atSlot_iff A native S ready s _ z x).mp found))
  constructor
  · refine a.trans ?_
    rw [ok]
    exact congrArg (fun w => some ((cableChip A S ready native groupKey vertex s x).neighbor,w)) (onWire (!s) x)
  · exact b.trans ((congrArg word host.symm).trans (onWire s x))

theorem chart_base (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap))
    (p : {e : Grain A // use e}) (found : atSlot A native S ready s (here v hi j) z=some p.val)
    (g' : (R).Good) (hv : v=bankV g') (hiEq : hi=bankH g') :
    DescentRotorWindowScore.interval Z.n (wireWord s (home A (endAt s p.val)))=
      (Z.goodLabel T g').val.1*2^remain+(Z.goodLabel T g').val.2 ↔ headAt p s=g' := by
  rw [rotorInterval A S ready digits Z T frm]
  refine ⟨fun eqn=>?_,fun eqn=>by rw [eqn]⟩
  apply Subtype.ext
  apply recover (m:=c) (R).b
  · rw [rotorHigh A S ready digits Z T frm,entered_digit A S ready digits native Z T frm s v hi j z p.val found s,
      Equiv.apply_symm_apply]
    exact (congrArg Fin.val (DescentPlainTerminal.high_join fit hi j)).trans (congrArg Fin.val hiEq)
  · have host:=(port_fst A s p.val).symm.trans (congrArg Prod.fst ((atSlot_iff A native S ready s _ z p.val).mp found))
    have atV : (A.pos (endAt s p.val)).2=v:=congrArg (fun z : old=>z.1.2) host
    have who:=rotorHost A S ready digits Z T frm p s
    rw [atV,hv,frm.host.apply_symm_apply] at who
    have rem (u : (R).Good) : (Z.goodLabel T u).val.2<2^remain :=
      (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right ((R).depth _) c))
    have score:=congrArg (fun z=>z%2^remain) eqn
    simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (rem _)] at score
    exact Prod.ext who score

variable (law : DonorOrder A digits) (sorted : SourceSorted W order) (tickets : Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order))
    (wide : max (max (Z.k-T.commonDepth) (2^Z.n)) (2^(Z.k-T.commonDepth))<2^field) (nWide : Z.n<field)

include room signBits onWire roster law sorted tickets wide nWide in
theorem paid_pair (s : Bool) (g' : (R).Good) (j : Fin L) (z : Fin (2*A.cap)) (e : Cells (R) s g')
    (found : atSlot A native S ready s (here (bankV g') (bankH g') j) z=some e.val) :
    pairCode (r := remain) (n:=Z.n) s (Z.goodLabel T g').val (board (bankV g') (bankH g')) (j,z) = DescentPackedRotorMatrix.pair (DescentChosenRouter.source (R) s g' e) (DescentChosenRouter.target (R) s g' e) := by
  let v:=bankV g'
  let hi:=bankH g'
  let p : {e : Grain A // use e}:=⟨e.val,paid (R) s g' e⟩
  let peer:=(cableChip A S ready native groupKey vertex s e.val).neighbor
  let encodedFields:=fieldRow (r := remain) (n:=Z.n) (board v hi) s (j,z) peer (chart s e.val)
  let col:=DescentPackedReservationColumn.column Z.n A.degree field (2^remain) (encode field _ encodedFields)
  have colRead:=column_here A S ready digits order Z T frm groupKey vertex word rank room signBits onWire
    f B wire K traffic weight roster law sorted tickets s v hi j z p found wide nWide
  have installed:=entry_physical A S ready digits native Z T frm groupKey vertex word rank room signBits onWire s v hi j z e.val found
  have arc:=chart_here A S ready digits order Z T frm groupKey vertex word rank room signBits onWire s v hi j z e.val found
  have flags:=(cell_mode A S ready digits Z T frm s e.val)
  have clear : bad (home A (endAt s e.val))=false ∧ bad (home A (endAt (!s) e.val))=false :=by
    exact Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr (fun marked => flags.mpr marked p.property))
  change entry (win v hi) s (j,z)=if use e.val then some (chart s e.val) else none at installed
  rw [ite_eq_left p.property] at installed
  rw [pairCode_some s _ (board v hi) (j,z) (chart s e.val) _ installed arc.1]
  change DescentPackedRotorMatrix.signedPair remain Z.n _ (DescentFallbackPeriod.localWord (win v hi) j) _ col.val=_
  rw [arc.2]
  simp only [peerShapeWord,clear.1,clear.2,Bool.toNat_false,Nat.add_zero]
  have endsEq : endAt s e.val=DescentResetAttachments.ends (Wold).graph s e.val:=by cases s <;> rfl
  let peerShape:=(shape (term (!s) (home A (endAt (!s) e.val)))).val
  have atRoot : term s (home A (endAt s e.val))=T.home (DescentResetAttachments.ends (Wold).graph s e.val) :=
    (cell_home A S ready digits Z T frm s e.val).trans (congrArg T.home endsEq)
  exact (congrArg (fun t => signedPair remain Z.n (Z.goodLabel T g').val (2*(shape t).val) (2*peerShape) col.val) atRoot).trans
    (signed_paid Z T s g' e peerShape col.val colRead)

theorem roster_slot (s : Bool) (g' : (R).Good) (e : Cells (R) s g') :
    let z:=landing s e.val
    atSlot A native S ready s (here (bankV g') (bankH g') z.1) z.2=some e.val := by
  let ok:=fun x : Grain A=>(R).owner s ((R).contact x)=.inl g'
  let x:=landing s e.val
  have eqn:=panel_at A native S ready digits frm.basis fit s (bankV g') (bankH g') ok
    (rotorCellsAt A S ready digits Z T frm s g') e.val e.property
  change (atSlot A native S ready s (here (bankV g') (bankH g') x.1) x.2).filter _=some e.val at eqn
  exact Option.eq_some_of_filter_eq_some eqn

private theorem slot_location (s : Bool) (g' : (R).Good) (j : Fin L) (z : Fin (2*A.cap)) (e : Grain A)
    (hit : atSlot A native S ready s (here (bankV g') (bankH g') j) z=some e) : landing s e=(j,z) := by
  have val:=(atSlot_iff A native S ready ..).mp hit
  unfold localAddress
  rw [val]
  refine Prod.ext ?_ rfl
  apply Fin.ext
  simp [subcell,donor,oldBlock,join,Equiv.symm_apply_apply,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]

include room signBits onWire roster law sorted tickets wide nWide in
theorem all_pairs (s : Bool) (g' : (R).Good) :
    (fun i : Fin (L*(2*A.cap))=>pairCode (r := remain) (n:=Z.n) s (Z.goodLabel T g').val
      (board (bankV g') (bankH g')) (finProdFinEquiv.symm i))=
      physical (R) s g' (physicalRoster A S ready digits order Z T frm s g') := by
  funext id
  obtain ⟨⟨j,z⟩,rfl⟩:=finProdFinEquiv.surjective id
  simp only [Equiv.symm_apply_apply]
  let v:=bankV g'
  let hi:=bankH g'
  let directory:=physicalRoster A S ready digits order Z T frm s g'
  by_cases active : ∃p : Cells (R) s g',directory.index p=finProdFinEquiv (j,z)
  · obtain ⟨p,same⟩:=active
    have address : landing s p.val=(j,z):=finProdFinEquiv.injective same
    have occupied:=roster_slot A S ready digits order Z T frm s g' p
    dsimp only at occupied
    rw [address] at occupied
    have res:=paid_pair A S ready digits order Z T frm groupKey vertex word rank room signBits onWire
      f B wire K traffic weight roster law sorted tickets wide nWide s g' j z p occupied
    exact res.trans (same ▸ (physical_at (R) s g' directory p).symm)
  · rw [physical,dite_eq_right active]
    cases dec : atSlot A native S ready s (here v hi j) z with
    | none=>
      have ghost:=entry_none A S ready digits native Z T frm groupKey vertex word rank room signBits s v hi j z dec
      apply pairCode_none
      exact ghost
    | some x=>
      have mark:=entry_physical A S ready digits native Z T frm groupKey vertex word rank room signBits onWire s v hi j z x dec
      change entry (win v hi) s (j,z)=(if use x then some (chart s x) else none) at mark
      by_cases good : use x
      · let p : {e : Grain A // use e}:=⟨x,good⟩
        have absent : headAt p s≠g' :=by
          intro atRoot
          let a : Cells (R) s g':=⟨x,(rotor_owned A S ready Z s p).trans (congrArg Sum.inl atRoot)⟩
          exact active ⟨a,congrArg finProdFinEquiv (slot_location A S ready digits order Z T frm s g' j z x dec)⟩
        have different:=((chart_base A S ready digits order Z T frm s v hi j z p dec g' rfl rfl).not).mpr absent
        have both:=chart_here A S ready digits order Z T frm groupKey vertex word rank room signBits onWire s v hi j z x dec
        rw [ite_eq_left good] at mark
        have changed := fun col=>show DescentPackedRotorMatrix.signedPair remain Z.n (Z.goodLabel T g').val
            (wireWord s (home A (endAt s x))) (wireWord (!s) (home A (endAt (!s) x))) col=0 by
          exact ite_eq_right (fun hit => different hit.2.2.2)
        rw [pairCode_some s _ (board v hi) (j,z) (chart s x) _ mark both.1]
        change DescentPackedRotorMatrix.signedPair remain Z.n _ (DescentFallbackPeriod.localWord (win v hi) j) _ _=0
        rw [both.2]
        apply changed
      · rw [ite_eq_right good] at mark
        apply pairCode_none
        exact mark

include room signBits onWire roster law sorted tickets wide nWide in
theorem installed_matrix (s : Bool) (g' : (R).Good) (i j : Fin Y) :
    DescentPackedResetRotorRoles.matrix Z.n (bins (L*(2*A.cap)))
      (DescentRotorWindowArchive.matrix remain Z.n s (Z.goodLabel T g').val (board (bankV g') (bankH g'))) i j=
      DescentBaseProfile.matrixOfBundles (source (R) s g') (DescentChosenRouter.target (R) s g') i j := by
  unfold DescentRotorWindowArchive.matrix
  rw [all_pairs A S ready digits order Z T frm groupKey vertex word rank room signBits onWire
    f B wire K traffic weight roster law sorted tickets wide nWide]
  apply physical_count

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
