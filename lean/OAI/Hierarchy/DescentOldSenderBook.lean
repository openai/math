import OAI.Hierarchy.DescentReachedOldSenderWords

namespace OAI
/-! # Transporting the measured sender board along the reached old grain-count equality -/
namespace Hierarchy.DescentOldSenderBook
open DescentOldContactSender DescentColonies DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D L cap n r c b Ht : ℕ} {V : Type}
structure Desk (D L cap n r c b Ht : ℕ) (V : Type)
    (value : Bool→Fin 2→V→Block c→Fin L→Fin (2*cap)→ℕ)
    (probe : (V→Block c→Measure D L cap n r b)→Prop) where
  Inputs : Type
  sample : Inputs→V→Block c→Measure D L cap n r b
  read : ∀(args : Inputs) s (j : Fin 2) v hi lo z,
    (point Ht s (sample args v hi) (lo,z) (Fin.castLE (by decide) j) : Cell b).val=value s j v hi lo z
  survey : ∀a,probe (sample a)

end
end Hierarchy.DescentOldSenderBook

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open DescentRotorWindowScore DescentPackedTicketChronology DescentPacking
open DescentRotorWindowArchive DescentCanonicalPorts DescentOldContactSender DescentContactSenderTicket DescentOldSenderBook
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
local notation "hostAt" => fun t=>frm.host.symm (T.code t).1
local notation "rootAt" => selectedRoot A S ready Z T
local notation "hs" => hostRoster A ids
local notation "ticketAt" => chartTicket A S ready digits native Z T frm groupKey vertex
local notation "rankAt" => leafRankAt A S ready Z T
local notation "R" => Z.placement
local notation "use" => useRotor (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "oldKey" => DescentOrderedReset.grains W A.grainCount order
local notation "arr" => leafPanel A S ready digits native Z T frm

/-- Only earlier measurements and their established geometry enter the desk. No sender
joint, fallback leaf ordinal or reciprocal return is supplied as an operand. -/
structure SenderInputs (field : ℕ) where
  word : old→ℕ
  rank : Fin H→Fin (width r Y A.degree)→Cell (Ht+2)
  room : ∀u,word u+1<2^field
  signBits : DescentSignedCableCodec.width A.degree A.cap≤field
  onWire : ∀s (e : Grain A),word (home A (DescentIssuedFallbackPanel.endSite A s e))=
    wireWord s (home A (DescentIssuedFallbackPanel.endSite A s e))
  f : ℕ
  B : ℕ
  wire : ℕ
  K : ℕ
  traffic : V→V→Block m→ℕ
  weight : V→Block m→ℕ
  roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (vertex.trans Fin.valEmbedding) A.near Z.n f B wire K (fun v z i=>(traffic v z i:ℝ)) A.degree weight
  law : DonorOrder A digits
  sorted : SourceSorted W order
  tickets : (R).OrderedTickets oldKey
  wide : max (max r Y) (2^r)<2^field
  nWide : Z.n<field
  books : ∀s t,DescentFallbackPeriod.key (Ht:=Ht) (l:=Z.layerBits) s (Z.fallLabel T t,(T.code t).2.2)
    (fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank (hostAt t) (rootAt t))=
      Z.fallbackKey T s t (arr s t)
  jointRoom : ∀s t,Z.senderJoint T s t<2^field
  heightRoom : Ht<2^field
  portRoom : A.degree≤2^field

def senderSample (info : SenderInputs A S ready digits order Z T frm groupKey vertex field) (v : V) (hi : Block c) :=
  withRank (boardFor (field:=field) A S ready digits order Z T frm groupKey vertex info.word info.rank v hi)
    (fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex info.word info.rank v hi)

def twoWords (s : Bool) (e : (Wold).graph.Edge) : Fin 2→ℕ :=
  ![Z.senderJoint T s ((R).contact e),Z.contactDepth s ((R).contact e)]

theorem sampled (info : SenderInputs A S ready digits order Z T frm groupKey vertex field)
    (s : Bool) (f : Fin 2) (v : V) (hi : Block c) (lo : Fin L) (z : Fin (2*A.cap)) :
    (point Ht s (senderSample A S ready digits order Z T frm groupKey vertex info v hi) (lo,z)
      (Fin.castLE (by decide) f):Cell field).val=
      (atSlot A native S ready s (here v hi lo) z).elim 0 (fun e=>twoWords A S ready Z T s e f) := by
  cases atOld : atSlot A native S ready s (here v hi lo) z with
  | none=>
    have hole:=sender_vacant A S ready digits order Z T frm groupKey vertex info.word info.rank info.room info.signBits s v hi lo z atOld
    simp only [senderSample,hole,Option.elim_none]
    exact Fin.val_cast_of_lt (Nat.two_pow_pos _)
  | some e=>
    have physical:=sender_at A S ready digits order Z T frm groupKey vertex info.word info.rank info.room info.signBits info.onWire
      info.f info.B info.wire info.K info.traffic info.weight info.roster info.law info.sorted info.tickets info.wide info.nWide
      info.books s v hi lo z e atOld
    have height : Z.contactDepth s ((R).contact e)<2^field:=by
      cases contact : (R).contact e with
      | inl i=>exact (Nat.zero_le Ht).trans_lt info.heightRoom
      | inr t=>exact (T.bookHeight s (fallEnd (R) s t)).trans_lt info.heightRoom
    fin_cases f <;>simp only [senderSample,physical,Option.elim_some,twoWords]
    all_goals first | exact Fin.val_cast_of_lt (info.jointRoom s _) | exact Fin.val_cast_of_lt height

theorem sampled_probe (info : SenderInputs A S ready digits order Z T frm groupKey vertex field)
    (s : Bool) (v : V) (hi : Block c) (lo : Fin L) (z : Fin (2*A.cap)) (e : Grain A)
    (found : atSlot A native S ready s (here v hi lo) z=some e) :
    let x:=senderSample A S ready digits order Z T frm groupKey vertex info v hi
    (point Ht s x (lo,z) 2:Cell field).val=(cableChip A S ready native groupKey vertex s e).neighbor.val ∧
    ∀t,(R).contact e=.inl t→
      (DescentReservedProbeInputs.value Z.n r s x.1 (lo,z) 0).val=t.2.val ∧
      (DescentReservedProbeInputs.value Z.n r s x.1 (lo,z) 1).val=(R).span t.1 := by
  intro x
  have physical:=sender_at A S ready digits order Z T frm groupKey vertex info.word info.rank info.room info.signBits info.onWire
    info.f info.B info.wire info.K info.traffic info.weight info.roster info.law info.sorted info.tickets info.wide info.nWide
    info.books s v hi lo z e found
  constructor
  · change (point Ht s (senderSample A S ready digits order Z T frm groupKey vertex info v hi) (lo,z) 2:Cell field).val=_
    change point Ht s (senderSample A S ready digits order Z T frm groupKey vertex info v hi) (lo,z)=_ at physical
    rw [physical]
    exact Fin.val_cast_of_lt ((cableChip A S ready native groupKey vertex s e).neighbor.isLt.trans_le info.portRoom)
  · intro t paid
    have yes : use e:=by by_contra miss;simp [Placement.contact,DescentChosenRouter.contact,miss] at paid
    let p : {e : Grain A // use e}:=⟨e,yes⟩
    have ticket : (R).ticket p=t:=by
      simp only [Placement.contact,DescentChosenRouter.contact,dite_eq_left yes,Sum.inl.injEq] at paid
      exact paid
    subst t
    exact reserved_probe_inputs A S ready digits order Z T frm groupKey vertex info.word info.rank info.room info.signBits
      info.onWire info.law info.sorted info.tickets s v hi lo z p found info.wide info.nWide

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentSixParty
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentColonies DescentGL
open DescentOldSenderBook DescentSIMDLookup DescentCompiler DescentOldContactSender
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃J×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (count : W.graph.Edge→ℕ) (countSame : count=A.grainCount) (unit wire : ℕ) (unitSame : unit=A.z) (wireSame : wire=A.wire)
    (fit : ∀e,W.graph.width e=count e*(unit*G.b))
local notation "old" => W.granular count (unit*G.b) fit
variable (Z : ResetInput (F:=F) (W.granular count (unit*G.b) fit) (q*wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "depth" => T.commonDepth
local notation "packed" => 2^(m-depth)
local notation "native" => order.trans Fin.valEmbedding
local notation "small" => frm.enough.trans (Nat.sub_le ..)
local notation "prior" => Equiv.sigmaCongrRight (fun e=>finCongr (congrFun countSame e))

include unitSame wireSame groupKey vertex in
def oldSenderDesk (field : ℕ) : Desk A.degree packed A.cap Z.n (Z.k-depth) depth field Ht V
    (fun s f v hi lo z=>(atSlot A native S ready s (donor digits frm.basis small v hi lo) z).elim 0
      (fun p=>let prev:=(prior).symm p; (![Z.senderJoint T s (Z.placement.contact prev),
        Z.contactDepth s (Z.placement.contact prev)] : Fin 2→ℕ) f))
    (fun sample=>∀s v hi lo z (p : Grain A),
      atSlot A native S ready s (donor digits frm.basis small v hi lo) z=some p→
        (point Ht s (sample v hi) (lo,z) 2:Cell field).val=(GroupStage.cableChip A S ready native groupKey vertex s p).neighbor.val ∧
        ∀t,Z.placement.contact ((prior).symm p)=.inl t→
        (DescentReservedProbeInputs.value Z.n (Z.k-depth) s (sample v hi).1 (lo,z) 0).val=t.2.val ∧
        (DescentReservedProbeInputs.value Z.n (Z.k-depth) s (sample v hi).1 (lo,z) 1).val=Z.placement.span t.1) := by
  subst count unit wire
  refine ⟨GroupStage.SenderInputs A S ready digits order Z T frm groupKey vertex field,
    GroupStage.senderSample A S ready digits order Z T frm groupKey vertex,?_,?_⟩
  · intro info side j v hi lo z
    have law:=GroupStage.sampled A S ready digits order Z T frm groupKey vertex info side j v hi lo z
    change _=(_ : Option (Grain A)).elim 0 _ at law ⊢
    exact law
  · intro info s v hi lo z p found
    rcases p with ⟨e,a⟩
    exact GroupStage.sampled_probe A S ready digits order Z T frm groupKey vertex info s v hi lo z ⟨e,a⟩ found

end
end Hierarchy.DescentSixParty

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentIssuedFallbackPanel DescentSIMDLookup DescentOldContactSender
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist field : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "words" => S.resetInputDigits ctl.base ctl.radix i
local notation "order" => input.order
local notation "groups" => Fin.valEmbedding (n:=S.groupCount i)
local notation "K" => 2*(A).cap
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "Ht" => GroupStage.depthBound D n f g

def senderDesk (field : ℕ) := oldSenderDesk (A) S input.valid words order B.count B.count_eq z w input.grain.symm
  input.edges.symm B.fit (Z) (T) B.frame groups input.vertex field

/-- The setup records the actual observed rotor board and the earlier measured leaf-rank
directory. The values of the emitted native cells follow from those inputs. -/
theorem reached_old_senders (setup : (senderDesk B field).Inputs)
    (xs : Fin (Fintype.card input.V)→Block (T).commonDepth→Fin (DescentOldContactSender.count (A).degree L (A).cap (Z).n ((Z).k-(T).commonDepth))→Cell field)
    (measured : ∀v hi,decode (xs (input.vertex v) hi)=(senderDesk B field).sample setup v hi) :
    OldSenderReads B (fun s (j : Fin 2) z v hi lo=>
      (point Ht s (decode (xs v hi)) (lo,z) (Fin.castLE (by decide) j):Cell field)) := by
  intro s bit v hi lo z
  exact (congrArg (fun board => (point Ht s board (lo,z) (Fin.castLE (by decide) bit) : Cell field).val)
    (measured v hi)).trans ((senderDesk B field).read setup s bit v hi lo z)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
