import OAI.Hierarchy.DescentClosedFreshArgumentKeys
import OAI.Hierarchy.DescentMeasuredFallbackSelection
import OAI.Hierarchy.DescentMeasuredRelayRows
import OAI.Hierarchy.DescentFallbackOperandBranch

namespace OAI
/-! # The original incoming-edge selection at a reached relay -/
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
local notation "rows_" => (cfg).relayRows x target
local notation "items_" => (cfg).relayItems x
local notation "fiber_" => {e : edge_ // loc_ e=t}
local notation "u_" => (blocks B).dst (trunkParent B t)
local notation "v_" => B.frame.host.symm (receiverRoot B u_).1
local notation "hi_" => (receiverRoot B u_).2
local notation "end_" e:arg => beforeStem B (e:edge_)
local notation "row_" e:arg => incomingIndex B (e:edge_)


def relayIndex : fiber_ ↪ Fin half_ :=by
  let resident (e : fiber_) : DescentParallelBase.Local (blocks B) u_ :=
    ⟨stemParent B (true,e.val),by rw [stem_one];decide,Or.inl ((incoming_home B t e.val).mpr e.property)⟩
  have atSlot (e : fiber_) : localRoster B u_ (resident e)=incomingCandidate B (row_ e.val):=
    Fin.ext (stem_number B u_ true e.val (resident e).property)
  refine ⟨fun e=>row_ e.val,?_⟩
  intro e g eqn
  have h:=(localRoster B u_).injective ((atSlot e).trans ((congrArg (incomingCandidate B) eqn).trans (atSlot g).symm))
  have tags:=(motherNames B).symm.injective (congrArg Subtype.val h)
  exact Subtype.ext (congrArg Prod.snd (Sum.inl.inj tags))

/-- Repeated original parallel edges remain separate because they occupy distinct signed slots. -/
def relayCoordinates (captured : ∀j,j∈rows_ ↔ ∃!e : edge_, loc_ e=t ∧ row_ e=j) :
    fiber_ ≃ ↥rows_ :=by
  let assign (e : fiber_) : ↥rows_:=⟨row_ e.val,(captured _).mpr ⟨e.val,⟨e.property,rfl⟩,by
    intro z hz
    have eqn : (⟨z,hz.1⟩ : fiber_)=e := (relayIndex B t).injective hz.2
    exact congrArg Subtype.val eqn⟩⟩
  apply Equiv.ofBijective assign
  constructor
  · intro a b same
    have eqn:row_ a.val=row_ b.val:=congrArg Subtype.val same
    obtain ⟨e,he,only⟩:=(captured (row_ b.val)).mp (assign b).property
    exact Subtype.ext ((only a.val ⟨a.property,eqn⟩).trans (only b.val ⟨b.property,rfl⟩).symm)
  · intro j
    obtain ⟨e,here,_⟩:=(captured j.val).mp j.property
    exact ⟨⟨e,here.1⟩,Subtype.ext here.2⟩

variable (captured : ∀ j, j ∈ ({sample with
  oldDegree := input.placement.degree
  oldCap := input.placement.cap
  donors := 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)
  fineBits := k
  fieldBits := field
  residual := B.reset.k-B.terminals.commonDepth
  maxDepth := GroupStage.depthBound D n f g}:DescentFallbackOperandBranch.Config).relayRows x target ↔
  ∃! e : (W.granular B.count (z*G.b) B.fit).graph.Edge,
    B.terminals.home ((W.granular B.count (z*G.b) B.fit).graph.dst e)=t ∧ incomingIndex B e=j)
local notation "coord" => relayCoordinates B sample field x target t captured
local notation "sortedKey" e:arg => ((items_ (row_ e)).key)
local notation "atSpot" e:arg => Stage.home (A) (W.graph.src (end_ e).1)

/-- Every comparison made by the compiler's literal finite selector can be read from its
original signed cable, old host insertion code and two published donor coordinates. -/
theorem relay_item_key {j : edge_} (atHome : loc_ j=t)
    (grp : Fin (S.groupCount i)↪ℕ)
    (signedWord : ((cfg).packet x (.inr (.inl (finProdFinEquiv.symm (row_ j))))).val=
      (DescentSignedCableCodec.encode (some (GroupStage.cableChip (A) S input.valid
        (input.order.trans Fin.valEmbedding) grp input.vertex true (end_ j)))).val)
    (hostRead : ((cfg).header x 3).val=hostCode
      (compress (hostDomain (A) input.vertex v_) (input.vertex v_).val) (decide (v_∉(A).near v_)))
    (groupWord : ((cfg).digit x (row_ j) 0).val=compress (groupDomain digits B.frame.basis fit v_ hi_)
      ((A).pos (W.graph.src (end_ j).1)).1.val)
    (fineWord : ((cfg).digit x (row_ j) 1).val=((A).block (W.graph.src (end_ j).1)).val) :
    sortedKey j=⟨compactStemSource B u_ (end_ j),(outgoingSlot (A) S input.valid input.order (end_ j)).val,(end_ j).2.val⟩:=by
  have present:=stem_cell B u_ true j (Or.inl ((incoming_home B t j).mpr atHome))
  exact DescentMeasuredOperandKey.key_at (A) S input.valid digits B.frame.basis fit
    (input.order.trans Fin.valEmbedding) grp input.vertex true (end_ j) v_ hi_ _ _ _ _
    present.1 signedWord hostRead groupWord fineWord

include captured in
/-- The actual incoming rank is a total chronological index into the paid present set. -/
theorem relay_lookup (age : 0< i) (sorted : SourceSorted W input.order)
    (keys : ∀e : fiber_,sortedKey e.val=
      ⟨compactStemSource B u_ (end_ e.val),(outgoingSlot (A) S input.valid input.order (end_ e.val)).val,(end_ e.val).2.val⟩)
    (e : edge_) (here : loc_ e=t) :
    select items_ rows_ (earlierIncoming B e)=some (row_ e) :=by
  let ix : fiber_ ↪ Fin _ := (Function.Embedding.subtype _).trans birth_
  have index (a : fiber_) : (coord a).val=row_ a.val:=rfl
  have ordered (a b : fiber_) :
      DescentFallbackItemSelect.before items_ (coord a).val (coord b).val ↔ ix a< ix b:=by
    rw [index,index]
    apply DescentFallbackItemSelect.chronological ix (fun j : fiber_=>row_ j.val) items_ _ a b
    intro x₀ y₀
    rw [keys,keys]
    have xHere : (blocks B).src (stemParent B (true,x₀.val))=u_:=(incoming_home B t x₀.val).2 x₀.property
    have yHere : (blocks B).src (stemParent B (true,y₀.val))=u_:=(incoming_home B t y₀.val).2 y₀.property
    have real:=stem_before_compact B age sorted u_ true x₀.val y₀.val (Or.inl xHere) (Or.inl yHere)
    rw [stem_ordinal,stem_ordinal,Nat.add_lt_add_iff_right,←beforeStem_code B x₀.val,←beforeStem_code B y₀.val] at real
    exact real.symm
  let j : fiber_:=⟨e,here⟩
  have equalRank:=rank_of_equiv items_ rows_ coord ix ordered j
  have equalCount : (Finset.univ.filter (fun a : fiber_=>ix a< ix j)).card=earlierIncoming B e:=by
    unfold earlierIncoming
    rw [here]
    apply Finset.card_bij (fun a _=>a.val)
    · intro a mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.property,(Finset.mem_filter.mp mem).2⟩
    · intro a _ b _ equal
      exact Subtype.ext equal
    · intro a mem
      obtain ⟨_,home_,earlier⟩:=Finset.mem_filter.mp mem
      exact ⟨⟨a,home_⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,earlier⟩,rfl⟩
  rw [←equalCount,←equalRank]
  exact select_read items_ rows_ (coord j).property


include captured in
/-- Padding beyond the relay's genuine number of nodes cannot select any signed grain. -/
theorem relay_absent_node (node : ℕ) (padded : Fintype.card fiber_≤node) :
    select items_ rows_ node=none:=by
  have size : (rows_).card=Fintype.card fiber_ :=
    (Fintype.card_coe rows_).symm.trans (Fintype.card_congr (coord).symm)
  unfold select
  rw [dite_eq_right]
  rintro ⟨j,mem,rfl⟩
  have smaller : rank items_ rows_ j<(rows_).card:=by
    apply Finset.card_lt_card
    apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2
    exact ⟨j,mem,by simp [DescentFallbackItemSelect.before,Key.irrefl]⟩
  omega

variable {H : ℕ} (padded : Fintype.card input.V≤H) (grp : Fin (S.groupCount i)↪ℕ)
local notation "vertex_" => input.vertex.trans (Fin.castLEEmb padded)
variable (snap : GroupStage.RootObservation input.placement S input.valid (S.resetInputDigits ctl.base ctl.radix i) (input.order.trans Fin.valEmbedding)
  grp (input.vertex.trans (Fin.castLEEmb padded)) B.reset B.terminals B.frame field)
local notation "ht_" => GroupStage.depthBound D n f g
local notation "ranks_" => DescentSharedBookScan.ranks (a:=B.reset.k-B.terminals.commonDepth)
  (Y:=2^B.reset.n) (D:=(A).degree) snap.chart (2^ht_) (ht_+2) snap.memory
local notation "root_" => (B.frame.host.symm (B.terminals.code t).1)
local notation "high_" => B.reset.rootBlock B.terminals (.inr t)

/-- The same saved old root packet supplies membership, chronological signed cable fields and
every padding bit. Only the previously published self code and two donor digits also enter. -/
theorem relay_collects (age : 0< i) (sorted : SourceSorted W input.order)
    (packet : (cfg).packet x=DescentFallbackPeriod.inputs (field:=field) snap.stencil snap.peers snap.marks
      (fun u j=>(ranks_ u j).val) (vertex_ root_) high_)
    (hostRead : ((cfg).header x 3).val=hostCode
      (compress (hostDomain (A) input.vertex v_) (input.vertex v_).val) (decide (v_∉(A).near v_)))
    (groupWord : ∀a : fiber_,((cfg).digit x (row_ a.val) 0).val=
      compress (groupDomain digits B.frame.basis fit v_ hi_) ((A).pos (W.graph.src (end_ a.val).1)).1.val)
    (fineWord : ∀a : fiber_,((cfg).digit x (row_ a.val) 1).val=((A).block (W.graph.src (end_ a.val).1)).val)
    (e : edge_) (atHome : loc_ e=t) :
    select items_ ((cfg).relayRows x (shortName B.terminals.commonDepth (B.terminals.code t)).2)
      (earlierIncoming B e)=some (row_ e) :=by
  have captured:=relay_rows_at B grp vertex_ snap sample t x packet
  apply relay_lookup B sample field x _ t captured age sorted _ e atHome
  intro a
  have touch : (blocks B).src (stemParent B (true,a.val))=u_:=(incoming_home B t a.val).mpr a.property
  have situated:=stem_cell B u_ true a.val (Or.inl touch)
  have root : receiverRoot B u_=((B.terminals.code t).1,high_):=by
    rw [←touch]
    have got:=(stem_receiver_root B true a.val).1
    change receiverRoot B ((blocks B).src (stemParent B (true,a.val))) =
      ((B.terminals.code (loc_ a.val)).1,B.reset.rootBlock B.terminals (.inr (loc_ a.val))) at got
    simpa only [a.property] using got
  have observed : (cfg).packet x=DescentFallbackPeriod.inputs (field:=field) snap.stencil snap.peers snap.marks
      (fun u j=>(ranks_ u j).val) (vertex_ v_) hi_:=by
    rw [root]
    exact packet
  change DescentMeasuredOperandKey.key (A).degree (A).cap k true
    ((cfg).packet x (.inr (.inl (finProdFinEquiv.symm (row_ a.val)))))
    ((cfg).header x 3) ((cfg).digit x (row_ a.val) 0) ((cfg).digit x (row_ a.val) 1)=_
  rw [observed]
  unfold incomingIndex
  rw [Equiv.symm_apply_apply]
  exact DescentMeasuredOperandKey.key_in_packet (A) S input.valid digits B.frame.basis fit
    (input.order.trans Fin.valEmbedding) grp input.vertex vertex_ snap.stencil snap.peers snap.marks
    (fun u j=>(ranks_ u j).val) snap.markRead snap.signedFits true (end_ a.val) v_ hi_ situated
    _ _ _ hostRead (groupWord a) (fineWord a)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
