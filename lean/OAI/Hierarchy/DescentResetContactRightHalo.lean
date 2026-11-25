import OAI.Hierarchy.DescentResetContactHaloWord
import OAI.Hierarchy.DescentResetSignedHaloOther

namespace OAI
/-! # The positive halo cargo on the two previous signed grain rows -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup DescentPackedZip
open DescentOldSenderReturn DescentCommonHost DescentResetCompactGeometry DescentResetStemCompactOrder DescentParallelBase DescentGroupPeerOrder
open DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel DescentResetOppositePayload DescentResetSignedHaloMatrix
open DescentPackedChildNeighbor.SIMD DescentSortedRoster DescentResetOriginHaloRAM DescentColonies.DynamicSplit
open private Hierarchy.DescentSixParty.ClosedReset.Window.rank_at_cast from OAI.Hierarchy.DescentResetContactHaloWord
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "A" => input.placement
local notation "ord" => input.order.trans Fin.valEmbedding
local notation "gr" => Function.Embedding.refl (Fin (S.groupCount i))
local notation "grp" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin grp) B.next.V k
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "IJ" => Fin L×Fin (2*(A).cap)
local notation "used"=>Fintype.card B.next.V
variable {H H0 a b t : ℕ} (prev : Fintype.card input.V≤H0) (next : Fintype.card B.next.V≤H)
local notation "hosts" => input.vertex.trans (Fin.castLEEmb prev)
local notation "adj" => hostRotor hosts (hostRoster A ((hosts).trans Fin.valEmbedding))
local notation "chart" => compactActorOrder B prev

/-- A raw donor may stand on either previous end, even on a loop.  The shared
matrix lookup always returns the target's ordinal in this receiver's old halo. -/
theorem target_halo_word (enough : DescentSignedCableCodec.width (A).degree (A).cap≤b)
    (queryWidth : (A).degree+1<2^a) (wordWidth : (A).degree+2<2^t) (u : Host) (s : Bool) (j : IJ)
    (e : (old).graph.Edge) (found : oldStemAt B u s j=some e) :
    let p:=port A s (beforeStem B e)
    let h:=((chart) u.1.2).castLE next
    let data:=rectangular (b:=b) A ord S input.valid gr hosts p.1.2 (address A ord S input.valid p).2 (hosts p.1.1.2) (gr p.1.1.1)
    let q:=Right.askedField (A).degree (A).cap b a data 0
    (lookup (short (b:=t) adj (haloHome B prev) h) q (List.finRange ((A).degree+1))).val=
      haloNumber B u ((Z).rootVertex T ((R).owner true ((R).contact e)))+1:=by
  intro p h field q
  obtain ⟨idx,hq,peer⟩:=Right.signed_halo A ord S input.valid gr hosts enough queryWidth s (beforeStem B e)
  rw [lookup_at _ _ idx hq,ite_eq_left (List.mem_finRange idx)]
  have eqn:=contact_old_slot_location B u s j e found
  have atHere:(port A s (beforeStem B e)).1.1.2=B.frame.host.symm (receiverRoot B u).1:=by
    exact (end_host B s e).trans (congrArg B.frame.host.symm (congrArg Prod.fst eqn).symm)
  have local_ : haloHome B prev ((chart) u.1.2)=hosts (B.frame.host.symm (receiverRoot B u).1):=by
    simp [haloHome,receiverRoot]
  have value : (short (b:=t) adj (haloHome B prev) h idx).val=DescentResetSignedHaloMatrix.rank adj (haloHome B prev) h idx:=
    Fin.val_cast_of_lt ((rank_bound adj (haloHome B prev) h idx).trans_lt wordWidth)
  rw [value]
  change DescentResetSignedHaloMatrix.rank adj (haloHome B prev) (((chart) u.1.2).castLE next) idx = _
  rw [Hierarchy.DescentSixParty.ClosedReset.Window.rank_at_cast,local_,←atHere,peer,atHere,end_host B true]
  rw [halo_old_rank B]
  exact congrArg (·+1) (measured_halo A input.vertex hosts adj (fun _=>rfl) (old_roster prev) _ _)

def receivedTargetHalo (chip : Cell b) (h : Fin H) : Cell t:=
  lookup (short (b:=t) adj (haloHome B prev) h) (Right.askedField (A).degree (A).cap b a chip 0) (List.finRange ((A).degree+1))

theorem raw_target_halo_at (enough : DescentSignedCableCodec.width (A).degree (A).cap≤b)
    (queryWidth : (A).degree+1<2^a) (wordWidth : (A).degree+2<2^t) (u : Host) (s : Bool) (j : Fin (L*(2*(A).cap)))
    (e : (old).graph.Edge) (found : originalDonor B u s j=some e) :
    let indices:=finProdFinEquiv.symm j
    let x:=previousSigned (b:=b) A ord S input.valid gr hosts (S.resetInputDigits ctl.base ctl.radix i)
      B.frame.basis (B.frame.enough.trans (Nat.sub_le ..)) indices.1 indices.2
      (hosts (B.frame.host.symm (receiverRoot B u).1)) (receiverRoot B u).2
    (receivedTargetHalo (a:=a) (t:=t) B prev x (((chart) u.1.2).castLE next)).val=
      haloNumber B u ((Z).rootVertex T ((R).owner true ((R).contact e)))+1:=by
  intro indices x
  unfold receivedTargetHalo
  rw [show x=_ from contact_old_signed (b:=b) B prev u s j e found]
  exact target_halo_word B prev next enough queryWidth wordWidth u s (finProdFinEquiv.symm j) e found

/-- The complete sender phase may first work on the preceding host itself, before the compact
successor host or its owner has appeared on the new raster. -/
theorem old_received_target_halo (u : Host) (x : Cell b) :
    lookup (short (b:=t) adj id (hosts (B.frame.host.symm (receiverRoot B u).1))) (Right.askedField (A).degree (A).cap b a x 0)
      (List.finRange ((A).degree+1))=receivedTargetHalo (a:=a) (t:=t) B prev x (((chart) u.1.2).castLE next):=by
  have eqn : haloHome B prev (chart u.1.2)=hosts (B.frame.host.symm (receiverRoot B u).1):=by
    simp [haloHome,receiverRoot]
  let query : Cell a := Right.askedField (A).degree (A).cap b a x 0
  have same := congrArg (fun v : Fin H0 =>
    lookup (short (b:=t) adj id v) query (List.finRange ((A).degree+1))) eqn.symm
  exact same.trans (old_lookup (b:=t) (a:=a) (H:=H) (D:=(A).degree) (S:=H0) (N:=used)
    adj (haloHome B prev) (chart u.1.2) next query)

theorem old_raw_target_halo_at (enough : DescentSignedCableCodec.width (A).degree (A).cap≤b)
    (queryWidth : (A).degree+1<2^a) (wordWidth : (A).degree+2<2^t) (u : Host) (s : Bool) (j : Fin (L*(2*(A).cap)))
    (e : (old).graph.Edge) (found : originalDonor B u s j=some e) :
    let indices:=finProdFinEquiv.symm j
    let v:=hosts (B.frame.host.symm (receiverRoot B u).1)
    let x:=previousSigned (b:=b) A ord S input.valid gr hosts (S.resetInputDigits ctl.base ctl.radix i)
      B.frame.basis (B.frame.enough.trans (Nat.sub_le ..)) indices.1 indices.2 v (receiverRoot B u).2
    (lookup (short (b:=t) adj id v) (Right.askedField (A).degree (A).cap b a x 0) (List.finRange ((A).degree+1))).val=
      haloNumber B u ((Z).rootVertex T ((R).owner true ((R).contact e)))+1:=by
  intro indices v x
  exact (congrArg Fin.val (old_received_target_halo (a:=a) (t:=t) B prev (H:=used) (le_refl _) u x)).trans
    (raw_target_halo_at B prev (H:=used) (le_refl _) enough queryWidth wordWidth u s j e found)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
