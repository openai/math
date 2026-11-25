import OAI.Hierarchy.DescentRotorWindowPairs

namespace OAI
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open DescentRotorWindowScore DescentPackedTicketChronology DescentPacking
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
local notation "native" => order.trans Fin.valEmbedding
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)
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


def previousDigit {c' : ℕ} (layout : Layout m) (small : c'≤ m) (hi : Block c') (j t : Block (m-c')) : Bool :=
  decide ((rearrange layout).symm (join small hi j)<(rearrange layout).symm (join small hi t))

def DonorOrder : Prop := ∀u v : W.graph.Site,(A.pos u).2=(A.pos v).2→
  (originalId W.graph.Site u<originalId W.graph.Site v ↔
    StarKeys.filled W.graph A.pos A.block digits u<StarKeys.filled W.graph A.pos A.block digits v)

theorem scheduledDonorOrder {tail : ℕ} (G₀ : GroupStage W G q ε (Fin (S.groupCount i)) V k)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (vtx : V↪Fin (Fintype.card V)) (coordinates : Function.Injective (fun t=>(G₀.pos t,G₀.block t)))
    (indexed : ∀u,originalId W.graph.Site u=(G₀.site vtx coordinates u).val) :
    DonorOrder G₀ (S.resetInputDigits baseGroups radix i) := by
  intro u v same
  change _ ↔ (StarKeys.filled W.graph G₀.pos G₀.block (S.resetInputDigits baseGroups radix i) u).val<_
  rw [old_inputDigit S baseGroups radix G₀ u,old_inputDigit S baseGroups radix G₀ v]
  exact old_source G₀ vtx coordinates indexed u v same

theorem window_prior (law : DonorOrder A digits) (s : Bool) (v : V) (hi : Block c) (j t : Fin L)
    (z w : Fin (2*A.cap)) (x y : {e : Grain A // use e})
    (hx : atSlot A native S ready s (here v hi j) z=some x.val)
    (hy : atSlot A native S ready s (here v hi t) w=some y.val)
    (pair : sameRotorPair A S ready Z y x.val) :
    prior (previousDigit frm.basis fit hi) (j,z) (t,w)
      (rotorEntry A S ready digits native Z T frm groupKey vertex s x.val)
      (rotorEntry A S ready digits native Z T frm groupKey vertex s y.val) ↔
    rotorPrevious A S ready order Z y x.val=true := by
  let u:=W.graph.src x.val.1
  let a:=W.graph.src y.val.1
  obtain ⟨_,pair⟩:=pair
  have one:=rotorHost A S ready digits Z T frm x false
  have two:=rotorHost A S ready digits Z T frm y false
  have sourceSite : (A.pos u).2=(A.pos a).2 :=
    frm.host.injective (one.symm.trans ((congrArg (fun z : Z.placement.Good=>z.val.1) (pair false)).trans two))
  have locX:=entered_digit A S ready digits native Z T frm s v hi j z x.val hx false
  have locY:=entered_digit A S ready digits native Z T frm s v hi t w y.val hy false
  have cmp:=law u a sourceSite
  have rev:=law a u sourceSite.symm
  change StarKeys.filled W.graph A.pos A.block digits u=_ at locX
  change StarKeys.filled W.graph A.pos A.block digits a=_ at locY
  rw [locX,locY] at cmp rev
  have eqn : originalId W.graph.Site u=originalId W.graph.Site a ↔ j=t := by
    constructor
    · intro same
      have atSame : u=a:=(originalId W.graph.Site).injective same
      have joined:=(rearrange frm.basis).symm.injective (locX.symm.trans ((congrArg (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) atSame).trans locY))
      simpa only [DescentPlainTerminal.low_join] using congrArg (@DescentPlainTerminal.low m c) joined
    · intro same
      subst t
      apply le_antisymm
      · exact le_of_not_gt (fun h=>lt_irrefl _ (rev.mp h))
      · exact le_of_not_gt (fun h=>lt_irrefl _ (cmp.mp h))
  change _ ↔ decide (DescentPackedTicketChronology.before (originalId W.graph.Site u) _ _ (originalId W.graph.Site a) _ _)=true
  simp only [prior,previousDigit,decide_eq_true_eq,DescentPackedTicketChronology.before,cmp,eqn]
  rfl

local notation "chart" => rotorEntry A S ready digits native Z T frm groupKey vertex

include room signBits onWire in
theorem counted_ticket (law : DonorOrder A digits) (sorted : SourceSorted W order)
    (tickets : Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order))
    (s : Bool) (p : {e : Grain A // use e}) :
    let v:=(A.pos (endAt s p.val)).2
    let hi:=rotorSourceHigh A S ready Z T s p
    let pslot:=localAddress («c» := T.commonDepth) A native S ready digits frm.basis s p.val
    let board:=win v hi
    let older:=previousDigit frm.basis fit hi
    (Z.placement.ticket p).2.val=(DescentRotorWindowScore.tally board s older pslot)%(Z.placement.span (Z.placement.ticket p).1) := by
  let v:=(A.pos (endAt s p.val)).2
  let hi:=rotorSourceHigh A S ready Z T s p
  let ps:=localAddress («c» := T.commonDepth) A native S ready digits frm.basis s p.val
  let eligible:=sameRotorPair A S ready Z p
  let scan:=panel A native S ready digits frm.basis fit s v hi eligible
  let older:=previousDigit frm.basis fit hi
  have self : eligible p.val:=⟨p.property,fun _=>rfl⟩
  have used:=panel_at A native S ready digits frm.basis fit s v hi eligible
    (sameRotorPair_source A S ready digits Z T frm s p) p.val self
  have hp : atSlot A native S ready s (here v hi ps.1) ps.2=some p.val:=by
    exact Option.eq_some_of_filter_eq_some used
  have actual:=entry_physical A S ready digits native Z T frm groupKey vertex word rank room signBits onWire s v hi ps.1 ps.2 p.val hp
  change entry (win v hi) s ps=(if use p.val then some (chart s p.val) else none) at actual
  rw [ite_eq_left p.property] at actual
  dsimp only
  rw [true_ticket_count A S ready digits order Z T frm tickets sorted s p]
  congr 2
  unfold DescentRotorWindowScore.tally
  rw [actual]
  apply congrArg Finset.card
  ext point
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rcases point with ⟨t,w⟩
  change (scan (t,w)).any (rotorPrevious A S ready order Z p) = true ↔
    (entry (win v hi) s (t,w)).any (fun a => decide
      (cohort a (chart s p.val) ∧ prior older (t,w) ps a (chart s p.val))) = true
  change (Option.filter (fun e => decide (eligible e))
    (atSlot A native S ready s (here v hi t) w)).any _ = true ↔ _
  cases h : atSlot A native S ready s (here v hi t) w with
  | none =>
    have dead := entry_none A S ready digits native Z T frm groupKey vertex word rank room signBits s v hi t w h
    rw [dead]
    rfl
  | some x =>
    have readEntry := entry_physical A S ready digits native Z T frm groupKey vertex word rank room signBits onWire s v hi t w x h
    change entry (win v hi) s (t,w) = (if use x then some (chart s x) else none) at readEntry
    rw [readEntry]
    by_cases accepted : use x
    · let e : {e : Grain A // use e} := ⟨x,accepted⟩
      have matched : cohort (chart s x) (chart s p.val) ↔ eligible x :=
        window_cohort A S ready digits native Z T frm groupKey vertex s v hi t ps.1 w ps.2 e p h hp
      by_cases yes : eligible x
      · have seq : prior older (t,w) ps (chart s x) (chart s p.val) ↔ rotorPrevious A S ready order Z p x = true :=
          window_prior A S ready digits order Z T frm groupKey vertex law s v hi t ps.1 w ps.2 e p h hp yes
        simp [accepted, yes, matched.mpr yes, seq]
      · simp [accepted, yes]
        exact fun hit => False.elim (yes (matched.mp hit))
    · have missed : ¬eligible x := fun h => accepted h.choose
      simp [accepted, missed]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
