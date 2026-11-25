import OAI.Hierarchy.DescentMeasuredRelayLookup
import OAI.Hierarchy.DescentStemCoordinateObserved
import OAI.Hierarchy.DescentResetPeerOldSelfWord

namespace OAI
/-! # The chronological digits of an old grain at its actual fallback relay -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentSharedCableNames DescentIssuedFallbackPanel
open DescentFallbackItemSelect DescentResetStemCompactOrder DescentPackedTicketChronology
open DescentResetTrunks DescentOrderedWords DescentStageEdgeReceipt DescentMeasuredOperandKey
open DescentSharedBookScan DescentRelativeContacts DescentResetStemWord DescentSharedCableNames.Stage DescentDenseHostOrder DescentSIMDLookup DescentGL DescentColonies DescentPacking
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "old_" => W.granular B.count (z*G.b) B.fit
local notation "edge_" => (old_).graph.Edge
local notation "loc_" => (fun e : edge_=>B.terminals.home ((old_).graph.dst e))
local notation "birth_" => DescentOrderedReset.grains W B.count B.order
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fit" => B.frame.enough.trans (Nat.sub_le ..)
local notation "cap_" => input.placement.cap
local notation "half_" => 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)*(2*cap_)
variable (sample : DescentFallbackOperandBranch.Config) (field : ℕ)
local notation "cfg" => ({sample with
  oldDegree := (A).degree
  oldCap := cap_
  donors := 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)
  fineBits := k
  fieldBits := field
  residual := B.reset.k-B.terminals.commonDepth
  maxDepth := GroupStage.depthBound D n f g}:DescentFallbackOperandBranch.Config)
variable (x : ({sample with
  oldDegree := input.placement.degree
  oldCap := input.placement.cap
  donors := 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)
  fineBits := k
  fieldBits := field
  residual := B.reset.k-B.terminals.commonDepth
  maxDepth := GroupStage.depthBound D n f g}:DescentFallbackOperandBranch.Config).Data B.reset.n) (target : DescentContacts.Endpoint (2^B.reset.n)) (t : B.reset.Fallback)
local notation "u_" => (blocks B).dst (trunkParent B t)
local notation "v_" => B.frame.host.symm (receiverRoot B u_).1
local notation "hi_" => (receiverRoot B u_).2
local notation "end_" e:arg => beforeStem B (e:edge_)
local notation "row_" e:arg => incomingIndex B (e:edge_)
local notation "address_" j:arg => finProdFinEquiv.symm (row_ j)
local notation "lo_" j:arg => (address_ j).1
local notation "actor_" => u_.1.2

/-- The original signed row at the incoming grain's own elected ordinal. -/
theorem relay_old_stem (j : edge_) (home : loc_ j=t) :
    oldStemAt B u_ true (address_ j)=some j := by
  have atSource := (incoming_home B t j).2 home
  let e : DescentParallelBase.Local (blocks B) u_ :=
    ⟨stemParent B (true,j),by rw [stem_one];decide,Or.inl atSource⟩
  have number : localRoster B u_ e=incomingCandidate B (row_ j) :=
    Fin.ext (stem_number B u_ true j e.property)
  have index : stemIndex B true (address_ j)=incomingCandidate B (row_ j) := by
    apply Fin.ext
    simp only [stemIndex,incomingCandidate,Fin.val_castLE,Equiv.apply_symm_apply]
    rfl
  have hit := (local_read B u_ _ e).2 (number.trans index.symm)
  obtain ⟨d,tag,read⟩ := (stem_at_iff B u_ true (address_ j) e).1 hit
  change stemParent B (true,j)=stemParent B (true,d) at tag
  have same : j=d :=congrArg Prod.snd
    (Sum.inl.inj ((motherNames B).symm.injective tag))
  subst d
  exact read

/-- The two integer digits prepared by the coordinate scans refer to the
original source of the edge, even when the receiver is its opposite endpoint. -/
theorem relay_donor_digits (H M b : ℕ) (j : edge_) (home : loc_ j=t) :
    (coords B H M b).value B.frame.basis 0 u_.2 (lo_ j) u_.1.1=
      compress (groupDomain digits B.frame.basis fit v_ hi_)
        ((A).pos (W.graph.src (end_ j).1)).1.val ∧
    (coords B H M b).value B.frame.basis 1 u_.2 (lo_ j) u_.1.1=
      ((A).block (W.graph.src (end_ j).1)).val :=by
  have read:=relay_old_stem B t j home
  constructor
  · rw [coords_group,stem_rank_digit B u_ (lo_ j),oldCell_read B u_ true (address_ j) j read]
  · rw [coords_fine]
    exact cell_fine B u_ true (address_ j) j read

/-- The actual dense receiver selects its old self-rank from the same captured
output as the signed register, including the old missing-loop correction. -/
theorem relay_self_digit {H : ℕ} (next : Fintype.card B.next.V≤H) :
    stemSelfDigit B (originalTrunkRack B) (((denseOrder B) actor_).castLE next)=
      hostCode (compress (hostDomain (A) input.vertex v_) (input.vertex v_).val)
        (decide (v_∉(A).near v_)) :=by
  have atActor : originalTrunkRack B (((denseOrder B) actor_).castLE next)=some actor_ :=by
    simp only [originalTrunkRack, Fin.val_castLE, dite_eq_left ((denseOrder B) actor_).isLt]
    exact congrArg some ((denseOrder B).symm_apply_apply actor_)
  rw [stemSelfDigit,atActor]
  rfl

local notation "native_" => input.order.trans Fin.valEmbedding
local notation "names_" grp:arg => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank grp (input.vertex.trans Fin.valEmbedding))

theorem relay_signed_at (grp : Fin (S.groupCount i)↪ℕ) (j : edge_) (home : loc_ j=t) :
    signedPanel (A) native_ S input.valid (names_ grp)
      (donor digits B.frame.basis fit v_ hi_ (lo_ j)) (address_ j).2=
    some (GroupStage.cableChip (A) S input.valid native_ grp input.vertex true (end_ j)) :=by
  have position:=stem_cell B u_ true j (Or.inl ((incoming_home B t j).2 home))
  simpa only [incomingIndex,Equiv.symm_apply_apply] using
    DescentMeasuredOperandKey.signed_at (A) S input.valid digits B.frame.basis fit native_ grp
      input.vertex true (end_ j) v_ hi_ position

/-- The four inputs to the relay key are the actual original signed chip,
the compact receiver's corrected self word, and the two coordinate digits. -/
theorem relay_key_observed {H : ℕ} (M b : ℕ) (next : Fintype.card B.next.V≤H)
    (grp : Fin (S.groupCount i)↪ℕ) (j : edge_) (home : loc_ j=t)
    (signed : ((cfg).packet x (.inr (.inl (address_ j)))).val =
      (DescentSignedCableCodec.encode (signedPanel (A) native_ S input.valid (names_ grp)
        (donor digits B.frame.basis fit v_ hi_ (lo_ j)) (address_ j).2)).val)
    (self : ((cfg).header x 3).val =
      stemSelfDigit B (originalTrunkRack B) (((denseOrder B) actor_).castLE next))
    (group : ((cfg).digit x (row_ j) 0).val =
      (coords B H M b).value B.frame.basis 0 u_.2 (lo_ j) u_.1.1)
    (fine : ((cfg).digit x (row_ j) 1).val =
      (coords B H M b).value B.frame.basis 1 u_.2 (lo_ j) u_.1.1) :
    ((cfg).relayItems x (row_ j)).key =
      ⟨compactStemSource B u_ (end_ j),
        (outgoingSlot (A) S input.valid input.order (end_ j)).val,(end_ j).2.val⟩ :=by
  rw [relay_signed_at B t grp j home] at signed
  have observed:=relay_donor_digits B t H M b j home
  exact relay_item_key B sample field x t home grp signed (self.trans (relay_self_digit B t next))
    (group.trans observed.1) (fine.trans observed.2)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
