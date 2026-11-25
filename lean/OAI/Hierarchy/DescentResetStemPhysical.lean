import OAI.Hierarchy.DescentPhysicalRotorEntries
import OAI.Hierarchy.DescentResetStemDecoder

namespace OAI
/-! # The selected old slot determines the physical endpoints of a reset stem -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open DescentRotorWindowScore DescentPackedTicketChronology
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
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
local notation "short" => fun t : Z.Fallback=>shortName c (T.code t)
local notation "term" => fallbackCell A S ready digits Z T frm
local notation "bad" => exceptionalCell A S ready digits Z T frm
local notation "shape" => chartShape A S ready Z T
local notation "wireWord" => peerShapeWord A S ready digits Z T frm
local notation "arrive" => chartArrival A S ready native groupKey vertex
local notation "physical" => signedPeer A native S ready names
local notation "hostAt" => fun t : Z.Fallback=>frm.host.symm (Prod.fst (T.code t))
local notation "rootAt" => selectedRoot A S ready Z T
local notation "hs" => hostRoster A ids
local notation "ticketAt" => chartTicket A S ready digits native Z T frm groupKey vertex
local notation "rankAt" => leafRankAt A S ready Z T
variable (word : Host J V k→ℕ) (rank : Fin H→Fin (width (Z.k-T.commonDepth) (2^Z.n) A.degree)→Cell (Ht+2))


local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank
local notation "use" => useRotor Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old
local notation "endAt" => DescentIssuedFallbackPanel.endSite (W:=W) A
variable (room : ∀u,word u+1<2^field) (signBits : DescentSignedCableCodec.width A.degree A.cap≤field)
variable (onWire : ∀s (e : Grain A),word (home A (endSite (W:=W) A s e))=peerShapeWord A S ready digits Z T frm s (home A (endSite (W:=W) A s e)))

open DescentResetStemDecoder

include room signBits in
theorem stem_probe_empty (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap))
    (empty : atSlot A native S ready s (here v hi j) z=none) :
    sample (win v hi) s j z=none := by
  apply DescentResetStemDecoder.empty
  have addr:=chartArrival_peer A S ready native groupKey vertex s (here v hi j) z
  rw [signedPeer_slot,empty,Option.map_none] at addr
  have dead : arrive s (here v hi j) z=none:=Option.map_eq_none_iff.mp addr
  simpa only [dead,Option.map_none] using
    window_arrival A S ready digits native Z T frm groupKey vertex word rank room signBits v hi j z s

include room signBits onWire in
theorem stem_probe_live (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap))
    (e : Grain A) (hit : atSlot A native S ready s (here v hi j) z=some e) :
    let atEnd:=endAt s e
    let t:=T.home atEnd
    sample (win v hi) s j z=some ((short t).2,decide (use e)) := by
  intro atEnd t
  let near:=home A atEnd
  let far:=home A (endAt (!s) e)
  have loc:=(atSlot_iff A native S ready s _ z e).mp hit
  have cell : here v hi j=near := (congrArg Prod.fst loc).symm.trans (port_fst A s e)
  have left:=window_own A S ready digits native Z T frm groupKey vertex word rank room v hi j
  rw [cell,onWire s e] at left
  have right:=window_arrival A S ready digits native Z T frm groupKey vertex word rank room signBits v hi j z s
  rw [arrival_at A S ready native groupKey vertex s e _ z hit,Option.map_some,onWire (!s) e] at right
  have src : (shape (term s near)).val=DescentFallbackShapeTable.cell r (short t).2 := by
    exact congrArg (fun a => (shape a).val) (cell_home A S ready digits Z T frm s e)
  have mode:=cell_mode A S ready digits Z T frm s e
  have chosen : (!(bad near || bad far))=decide (use e) := by
    by_cases pay : use e
    · have off : (bad near || bad far)=false := by
        cases test : (bad near || bad far)
        · rfl
        · exact False.elim ((mode.mpr test) pay)
      simp [off,pay]
    · have off : (bad near || bad far)=true:=mode.mp pay
      simp [off,pay]
  rw [←chosen]
  apply occupied (win v hi) s j z (cableChip A S ready native groupKey vertex s e).neighbor
    (short t).2 (shape (term (!s) far)).val (bad near) (bad far)
  · change DescentFallbackPeriod.localWord (win v hi) j =
        2*(shape (term s near)).val+(bad near).toNat at left
    exact left.trans (congrArg (fun a => 2*a+(bad near).toNat) src)
  · exact right
  · exact Nat.sub_le_sub_right (T.codeLegal t).2.1 _
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)

include room signBits onWire in
theorem stem_probe_nodes (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap))
    (e : Grain A) (hit : atSlot A native S ready s (here v hi j) z=some e) :
    let t:=T.home (endAt s e)
    (sample (win v hi) s j z).bind (nodes Z.graph s (frm.host v))=some
      (.trunk s (short t),DescentCommonHost.publicNode Z.placement Z.graph c T.code s (Z.placement.input s e)) := by
  intro t
  rw [stem_probe_live A S ready digits native Z T frm groupKey vertex word rank room signBits onWire s v hi j z e hit]
  have loc:=(atSlot_iff A native S ready s _ z e).mp hit
  have near : (A.pos (endAt s e)).2=v := congrArg (fun x : old=>x.1.2)
    ((port_fst A s e).symm.trans (congrArg Prod.fst loc))
  have host : (short t).1=frm.host v := (frm.homeHost _).trans (congrArg frm.host near)
  have dest:=DescentChosenRouter.public_read Z.placement T.code T.source s e
  have attach : Z.placement.fall s (Z.placement.old s e)=t := by
    cases s <;> exact (T.attach _ _).symm
  have full : DescentRelativeContacts.shortName c (DescentChosenRouter.publicAddress Z.placement T.code (Z.placement.input s e))=short t :=
    congrArg (DescentRelativeContacts.shortName c) (dest.trans (congrArg T.code attach))
  have kind : (Z.placement.input s e).isLeft=decide (use e) := by
    by_cases yes : use e <;> simp [DescentChosenRouter.Placement.input,DescentChosenRouter.pub,yes]
  have real:=nodes_public Z.placement Z.graph c T.code s (Z.placement.input s e)
  dsimp only at real
  rw [full,kind] at real
  rw [←host]
  exact real

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
