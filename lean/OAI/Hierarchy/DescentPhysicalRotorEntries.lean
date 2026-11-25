import OAI.Hierarchy.DescentRotorWindowBases
import OAI.Hierarchy.DescentFallbackWindowGeometry

namespace OAI
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

include signBits in
theorem rotor_chip (v : V) (hi : Block c) (j : Fin L) (q : Fin (2*A.cap)) :
    DescentFallbackPeriod.signed (win v hi) j q=shelved (here v hi j) q := by
  have legal:=(DescentSignedCableCodec.encode (shelved (here v hi j) q)).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) signBits)
  simp only [DescentFallbackPeriod.signed,fallbackWindow,DescentFallbackPeriod.inputs,
    fallbackPadded_hit,Fin.val_cast_of_lt legal,Fin.cast_val_eq_self,DescentSignedCableCodec.decode_encode]

def cableChip (s : Bool) (e : Grain A) :=
  live A native S ready names (port A s e).1 (port A s e).2

theorem chip_source (e : Grain A) (s : Bool) :
    (cableChip A S ready native groupKey vertex s e).sourceWire=
      outgoing A native S ready ⟨e.1,Nat.zero_lt_of_lt e.2.isLt⟩ ∧
    (cableChip A S ready native groupKey vertex s e).within.val=e.2.val := by cases s <;> exact ⟨rfl,rfl⟩

theorem chip_at (s : Bool) (e : Grain A) (u : old) (q : Fin (2*A.cap))
    (hit : atSlot A native S ready s u q=some e) :
    shelved u q=some (cableChip A S ready native groupKey vertex s e) := by
  have ident:=(atSlot_iff A native S ready s u q e).mp hit
  have back:=signed_read A native S ready names (port A s e).1 (port A s e).2
  change shelved (address A native S ready (port A s e)).1 (address A native S ready (port A s e)).2=_ at back
  rwa [ident] at back

theorem arrival_at (s : Bool) (e : Grain A) (u : old) (z : Fin (2*A.cap))
    (hit : atSlot A native S ready s u z=some e) :
    arrive s u z=some ((cableChip A S ready native groupKey vertex s e).neighbor,home A (endAt (!s) e)) := by
  have dest:=chartArrival_peer A S ready native groupKey vertex s u z
  rw [signedPeer_slot,hit,Option.map_some] at dest
  obtain ⟨⟨j,b⟩,yes,far⟩:=Option.map_eq_some_iff.mp dest
  have chip:=chip_at A S ready native groupKey vertex s e u z hit
  have same:=yes
  unfold chartArrival at same
  rw [chip] at same
  simp only [bind,Option.bind_some] at same
  split at same
  · cases dest : hostRoster A ids u.1.2 (cableChip A S ready native groupKey vertex s e).neighbor with
    | none => simp [dest] at same
    | some w =>
      simp [dest] at same
      exact yes.trans (congrArg some (Prod.ext same.1.symm far))
  · contradiction

include room signBits in
theorem entry_none (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap))
    (empty : atSlot A native S ready s (here v hi j) z=none) :
    entry (win v hi) s (j,z)=none := by
  have addr:=chartArrival_peer A S ready native groupKey vertex s (here v hi j) z
  rw [signedPeer_slot,empty,Option.map_none] at addr
  have dead : arrive s (here v hi j) z=none:=Option.map_eq_none_iff.mp addr
  have peer:=window_arrival A S ready digits native Z T frm groupKey vertex word rank room signBits v hi j z s
  rw [dead,Option.map_none] at peer
  unfold entry
  cases DescentFallbackPeriod.signed (win v hi) j z <;> simp [peer]

include room signBits onWire in
theorem entry_physical (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap)) (e : Grain A)
    (hit : atSlot A native S ready s (here v hi j) z=some e) :
    entry (win v hi) s (j,z)=if use e then some
      ⟨(cableChip A S ready native groupKey vertex s e).neighbor.val,
       DescentRotorWindowScore.interval Z.n (wireWord s (home A (endAt s e))),
       DescentRotorWindowScore.interval Z.n (wireWord (!s) (home A (endAt (!s) e))),
       (outgoing A native S ready ⟨e.1,Nat.zero_lt_of_lt e.2.isLt⟩).val,e.2.val⟩ else none := by
  have ident:=(atSlot_iff A native S ready s _ z e).mp hit
  have hereEq : here v hi j=home A (endAt s e) :=
    (congrArg Prod.fst ident).symm.trans (port_fst A s e)
  have marked:=chip_at A S ready native groupKey vertex s e _ z hit
  have remote:=arrival_at A S ready native groupKey vertex s e _ z hit
  have chip:=rotor_chip A S ready digits native Z T frm groupKey vertex word rank signBits v hi j z
  have peer:=window_arrival A S ready digits native Z T frm groupKey vertex word rank room signBits v hi j z s
  have own:=window_own A S ready digits native Z T frm groupKey vertex word rank room v hi j
  rw [marked] at chip
  rw [remote,Option.map_some,onWire (!s) e] at peer
  rw [hereEq,onWire s e] at own
  have mode : (wireWord s (home A (endAt s e))%2=0 ∧ wireWord (!s) (home A (endAt (!s) e))%2=0) ↔ use e := by
    have compare:=cell_mode A S ready digits Z T frm s e
    cases ha : bad (home A (endAt s e)) <;> cases hb : bad (home A (endAt (!s) e)) <;>
      simp [peerShapeWord,ha,hb] at compare ⊢ <;> tauto
  have values:=chip_source A S ready native groupKey vertex e s
  simp only [entry,chip,peer,bind,Option.bind_some,own,values.1,values.2,mode]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
