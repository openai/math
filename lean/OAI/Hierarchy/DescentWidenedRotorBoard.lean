import OAI.Hierarchy.DescentRotorInstalledColumn

namespace OAI
/-! # Widening the true rotor packet to the instruction word -/
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

include room signBits in
/-- Every numerical field of the original public rotor archive keeps its value
when the packed result is widened for the common instruction register. -/
theorem board_widened {wider : ℕ} (grow : field≤wider) (resources : max (max remain Y) (2^remain)<2^field)
    (v : V) (hi : Block c) (j : DescentRotorWindowArchive.Input A.degree L A.cap) :
    (boardFor (field:=wider) A S ready digits order Z T frm groupKey vertex word rank v hi j).val=
      (boardFor (field:=field) A S ready digits order Z T frm groupKey vertex word rank v hi j).val:=by
  have capBits : 2^field≤2^wider:=Nat.pow_le_pow_right (by decide) grow
  have same (a : ℕ) (fits : a<2^field) : (a:Cell wider).val=(a:Cell field).val:=by
    rw [Fin.val_cast_of_lt fits,Fin.val_cast_of_lt (fits.trans_le capBits)]
  rcases j with ((i|⟨j,i⟩)|⟨i,q⟩)|(⟨i,k⟩|⟨query,across,axis⟩)
  · simp only [boardFor,observed,fallbackWindow,DescentFallbackPeriod.inputs,fallbackPadded_hit]
    exact same _ (Nat.lt_of_succ_lt (room _))
  · simp only [boardFor,observed,fallbackWindow,DescentFallbackPeriod.inputs,fallbackPadded_hit]
    cases hq:hs v j with
    | none=>rfl
    | some v' =>
      simp only [Option.map_some,Option.elim_some,fallbackPadded_hit]
      simpa only [Nat.cast_add,Nat.cast_one] using same _ (room (here v' hi i))
  · simp only [boardFor,observed,fallbackWindow,DescentFallbackPeriod.inputs,fallbackPadded_hit]
    exact same _ ( (Fin.isLt (DescentSignedCableCodec.encode (shelved (here v hi i) q))).trans_le (Nat.pow_le_pow_right (by decide) signBits))
  · change (((previousDigit frm.basis fit hi i k).toNat:ℕ):Cell wider).val=_
    have bit (b : Bool) : b.toNat≤1:=by cases b <;> decide
    exact same _ ((bit _).trans_lt (by have p₀:=Nat.two_pow_pos remain;omega))
  · change (peerData (a:=wider) A S ready digits Z T frm vertex v query across axis).val=
      (peerData (a:=field) A S ready digits Z T frm vertex v query across axis).val
    simp only [peerData]
    cases next₀:hs v query with
    | none=>rfl
    | some dest =>
      cases next₁:hs v across with
      | none=>rfl
      | some oldV =>
        let box:=DescentShortReservationPeer.compare (2^remain) (vertex oldV).val (vertex dest).val
        have depth:Z.placement.b (frm.host oldV)-T.commonDepth≤remain:=Nat.sub_le_sub_right (Z.placement.depth _) _
        have width:min (T.columns.size (frm.host v) (frm.host oldV)) Y≤Y:=min_le_right _ _
        have fst:box.first≤2^remain:=min_le_right _ _
        have snd:box.second≤2^remain:=min_le_right _ _
        have one:=Nat.two_pow_pos remain
        have bit (b : Bool) : b.toNat≤1:=by cases b <;> decide
        apply same
        change ![Z.placement.b (frm.host oldV)-T.commonDepth,min (T.columns.size (frm.host v) (frm.host oldV)) Y,
          box.first,box.second,box.less.toNat,box.same.toNat] axis<2^field
        have capRoom := (max_lt_iff.mp resources).1
        have powRoom := (max_lt_iff.mp resources).2
        have bitRoom : 1 < 2^field := Nat.lt_of_le_of_lt one powRoom
        fin_cases axis
        · exact depth.trans_lt (max_lt_iff.mp capRoom).1
        · exact width.trans_lt (max_lt_iff.mp capRoom).2
        · exact fst.trans_lt powRoom
        · exact snd.trans_lt powRoom
        · exact (bit _).trans_lt bitRoom
        · exact (bit _).trans_lt bitRoom

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
