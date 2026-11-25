import OAI.Hierarchy.DescentPhysicalRotorEntries

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
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht)
  (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2)
  (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "c" => T.commonDepth
local notation "L" => 2^(m-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "old" => Host J V k
local notation "here" => donor digits frm.basis fit
local notation "wireWord" => peerShapeWord A S ready digits Z T frm
local notation "hs" => hostRoster A ids
local notation "use" => useRotor Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old
local notation "endAt" => DescentIssuedFallbackPanel.endSite A

private theorem entered (s : Bool) (v : V) (hi : Block c) (j : Fin L) (slot : Fin (2*A.cap)) (e : Grain A)
    (hit : atSlot A native S ready s (here v hi j) slot=some e) :
    home A (endAt s e)=here v hi j :=
  (port_fst A s e).symm.trans (congrArg Prod.fst ((atSlot_iff A native S ready s _ slot e).mp hit))

theorem wireDigit (s : Bool) (e : Grain A) :
    StarKeys.filled W.graph A.pos A.block digits (endAt s e)=StarKeys.filled W.graph A.pos A.block digits (W.graph.src e.1) := by
  obtain ⟨v,_,peer⟩:=Finset.mem_map.mp (A.peers e.1).1
  have same := congrArg (fun p : J×V=>p.1) peer
  change (A.pos (W.graph.src e.1)).1=(A.pos (W.graph.dst e.1)).1 at same
  cases s
  · rfl
  · unfold StarKeys.filled
    change digits.symm ((A.pos (W.graph.dst e.1)).1,A.block (W.graph.dst e.1))=_
    rw [←same,←A.same e.1]

theorem entered_digit (s : Bool) (v : V) (hi : Block c) (j : Fin L) (slot : Fin (2*A.cap)) (e : Grain A)
    (hit : atSlot A native S ready s (here v hi j) slot=some e) (t : Bool) :
    StarKeys.filled W.graph A.pos A.block digits (endAt t e)=(rearrange frm.basis).symm (join fit hi j) := by
  rw [wireDigit A digits t e,←wireDigit A digits s e]
  change oldBlock digits (home A (endAt s e))=_
  rw [entered A S ready digits native Z T frm s v hi j slot e hit]
  simp [oldBlock,donor]

private theorem remote_slot (u w : V) (j j' : Fin A.degree)
    (one : hs u j=some w) (two : hs u j'=some w) : j=j' := by
  unfold hostRoster at one two
  split at one
  · rename_i live
    split at two
    · rename_i next
      have eqn : live.choose=next.choose:=Subtype.ext ((Option.some.inj one).trans (Option.some.inj two).symm)
      exact live.choose_spec.symm.trans ((congrArg (hostSlot A ids u) eqn).trans next.choose_spec)
    · contradiction
  · contradiction

private theorem remote_at (s : Bool) (v : V) (hi : Block c) (j : Fin L) (slot : Fin (2*A.cap)) (e : Grain A)
    (hit : atSlot A native S ready s (here v hi j) slot=some e) :
    hs v (cableChip A S ready native groupKey vertex s e).neighbor=some (A.pos (endAt (!s) e)).2 := by
  have found:=arrival_at A S ready native groupKey vertex s e (here v hi j) slot hit
  exact (chartArrival_host A S ready digits native Z T frm groupKey vertex s _ _ _ _ found).1

def rotorEntry (s : Bool) (e : Grain A) : Entry :=
  ⟨(cableChip A S ready native groupKey vertex s e).neighbor.val,
    DescentRotorWindowScore.interval Z.n (wireWord s (home A (endAt s e))),
    DescentRotorWindowScore.interval Z.n (wireWord (!s) (home A (endAt (!s) e))),
    (outgoing A native S ready ⟨e.1,Nat.zero_lt_of_lt e.2.isLt⟩).val,e.2.val⟩

theorem window_cohort (s : Bool) (v : V) (hi : Block c) (j k' : Fin L) (z w : Fin (2*A.cap))
    (p t : {e : Grain A // use e})
    (hp : atSlot A native S ready s (here v hi j) z=some p.val)
    (ht : atSlot A native S ready s (here v hi k') w=some t.val) :
    cohort (rotorEntry A S ready digits native Z T frm groupKey vertex s p.val)
      (rotorEntry A S ready digits native Z T frm groupKey vertex s t.val) ↔ sameRotorPair A S ready Z t p.val := by
  let headAt:=base Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old
  have high (side : Bool) :
      group c (rearrange frm.basis (StarKeys.filled W.graph A.pos A.block digits (endAt side p.val)))=
      group c (rearrange frm.basis (StarKeys.filled W.graph A.pos A.block digits (endAt side t.val))) := by
    rw [entered_digit A S ready digits native Z T frm s v hi j z p.val hp side,
      entered_digit A S ready digits native Z T frm s v hi k' w t.val ht side]
    simp only [Equiv.apply_symm_apply]
    exact congrArg Fin.val ((DescentPlainTerminal.high_join fit hi j).trans (DescentPlainTerminal.high_join fit hi k').symm)
  have hereP:=entered A S ready digits native Z T frm s v hi j z p.val hp
  have hereT:=entered A S ready digits native Z T frm s v hi k' w t.val ht
  have sameV : (A.pos (endAt s p.val)).2=(A.pos (endAt s t.val)).2 :=
    (congrArg (fun a : old=>a.1.2) hereP).trans (congrArg (fun a : old=>a.1.2) hereT).symm
  have rp:=remote_at A S ready digits native Z T frm groupKey vertex s v hi j z p.val hp
  have rt:=remote_at A S ready digits native Z T frm groupKey vertex s v hi k' w t.val ht
  have nearEq : (cableChip A S ready native groupKey vertex s p.val).neighbor.val=
      (cableChip A S ready native groupKey vertex s t.val).neighbor.val ↔
      (A.pos (endAt (!s) p.val)).2=(A.pos (endAt (!s) t.val)).2 := by
    constructor
    · intro eqn
      rw [Fin.ext eqn] at rp
      exact Option.some.inj (rp.symm.trans rt)
    · intro eqn
      exact congrArg Fin.val (remote_slot A vertex v _ _ _ (rp.trans (congrArg some eqn)) rt)
  have own:=rotorInterval_eq A S ready digits Z T frm p t s (high s)
  have peer:=rotorInterval_eq A S ready digits Z T frm p t (!s) (high (!s))
  have eqv : sameRotorPair A S ready Z t p.val ↔ headAt p s=headAt t s ∧ headAt p (!s)=headAt t (!s) := by
    constructor
    · rintro ⟨_,all⟩;exact ⟨all s,all (!s)⟩
    · rintro ⟨first,last⟩;refine ⟨p.property,?_⟩;intro side
      cases s <;> cases side <;> first | exact first | exact last
  constructor
  · rintro ⟨sameNeighbor,sameOwn,samePeer⟩
    exact eqv.mpr ⟨own.mpr ⟨sameV,sameOwn⟩,peer.mpr ⟨nearEq.mp sameNeighbor,samePeer⟩⟩
  · intro samePair
    obtain ⟨first,last⟩ := eqv.mp samePair
    obtain ⟨remote,interval⟩ := peer.mp last
    exact ⟨nearEq.mpr remote,(own.mp first).2,interval⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
