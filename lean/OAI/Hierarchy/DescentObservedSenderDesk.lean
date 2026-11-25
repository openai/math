import OAI.Hierarchy.DescentOldSenderBook
import OAI.Hierarchy.DescentPreparedSenderPrior
import OAI.Hierarchy.DescentResetPeerObservedFallback
import OAI.Hierarchy.DescentRotorReservationSources

namespace OAI
/-! # The measured signed sender on its original padded host and rank directory -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentGL DescentColonies DescentIssuedFallbackPanel DescentRosterOrder DescentStageEdgeReceipt
open DescentResetHostSize DescentSIMDLookup DescentSharedBookScan DescentSharedCableNames.Stage DescentCompiler
open DescentOldContactSender DescentFallbackPeriod DescentFallbackPeriod.Projected DescentGroupPeerOrder
open DescentRotorWindowArchive DescentPackedTicketChronology DescentPacking
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i m g h C Ht H H' field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
  (digits : Block m≃J×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
local notation "native" => order.trans Fin.valEmbedding
local notation "old" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
  (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
  (group : J↪ℕ) (name : V↪Fin H) (pad : H≤H')
local notation "large" => name.trans (Fin.castLEEmb pad)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "Y" => 2^Z.n
local notation "L" => 2^(m-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
variable (obs : RootObservation A S ready digits (order.trans Fin.valEmbedding) group (name.trans (Fin.castLEEmb pad)) Z T frm field)
local notation "ranksAt" => ranks (a:=r) («Y»:=Y) (D:=A.degree) obs.chart (2^Ht) (Ht+2) obs.memory
local notation "rank₀" => fun t : Fin H=>(ranksAt) (t.castLE pad)
local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm group name obs.word rank₀
local notation:max "pkt" v:arg hi:arg => (inputs (field:=field) obs.stencil obs.peers obs.marks (fun u j=>((ranksAt) u j).val) ((large) v) hi :
  Packet A.degree L A.cap Z.n r field)

theorem desk_window (v : V) (hi : Block c) : pkt v hi=win v hi:=by
  funext j
  rcases j with (lo|⟨k,lo⟩)|(⟨lo,z⟩|j)
  · simp only [inputs,fallbackWindow,fallbackPadded_hit]
    exact congrArg (fun value : ℕ => (value : Cell field)) (obs.stencilRead v hi lo)
  · simp only [inputs,obs.rosterRead,fallbackWindow,fallbackPadded_hit]
    change ((Option.map _ (hostRoster A (name.trans Fin.valEmbedding) v k)).elim 0 _:Cell field)=_
    cases peer : hostRoster A (name.trans Fin.valEmbedding) v k with
    | none => rfl
    | some u =>
      simp only [Option.map_some,Option.elim_some,fallbackPadded_hit]
      exact congrArg (fun value : ℕ => ((value : Cell field) + 1)) (obs.stencilRead u hi lo)
  · simp only [inputs,fallbackWindow,fallbackPadded_hit]
    exact congrArg (fun mark => ((DescentSignedCableCodec.encode mark).val : Cell field)) (obs.markRead v hi lo z)
  · rfl

variable (f price wire K : ℕ) (traffic : V→V→Block m→ℕ) (weight : V→Block m→ℕ)
  (rels : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (name.trans Fin.valEmbedding) A.near Z.n f price wire K (fun v u j=>(traffic v u j:ℝ)) A.degree weight)
  (law : DonorOrder A digits) (sorted : SourceSorted W order)
  (ticket : Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order))
  (wide : max (max (Z.k-T.commonDepth) (2^Z.n)) (2^(Z.k-T.commonDepth))<2^field) (nWide : Z.n<field)
  (jWide : ∀s t,Z.senderJoint T s t<2^field) (hWide : Ht<2^field) (dWide : A.degree≤2^field)

/-- Its ranked fallback labels are read from exactly the scalar chart used by the
observed sender. Host padding changes only indices outside the old host image. -/
def observedSenderInputs : SenderInputs A S ready digits order Z T frm group name field where
  word:=obs.word
  rank:=rank₀
  room:=obs.wordFits
  signBits:=obs.signedFits
  onWire:=obs.onWire
  f:=f
  B:=price
  wire:=wire
  K:=K
  traffic:=traffic
  weight:=weight
  roster:=rels
  law:=law
  sorted:=sorted
  tickets:=ticket
  wide:=wide
  nWide:=nWide
  books:=by
    intro side t
    have actual:=observed_live_root A S ready digits native group large Z T frm obs side t
    simp only [RootObservation.packed,packet_encode] at actual
    exact (congrArg (key (Ht:=Ht) (l:=Z.layerBits) side (Z.fallLabel T t,(T.code t).2.2))
      (desk_window A S ready digits order Z T frm group name pad obs (frm.host.symm (T.code t).1)
        (Z.rootBlock T (.inr t))).symm).trans actual
  jointRoom:=jWide
  heightRoom:=hWide
  portRoom:=dWide

local notation "setup" => observedSenderInputs A S ready digits order Z T frm group name pad obs f price wire K
  traffic weight rels law sorted ticket wide nWide jWide hWide dWide

include rels law sorted ticket wide nWide jWide hWide dWide in
theorem observed_sender_words (quota : Fin H'→Fin A.degree→Fin A.degree→Fin 6→Cell field)
    (issued : ∀v j l s,quota (large v) j l s=peerData (a:=field) A S ready digits Z T frm name v j l s)
    (v : V) (hi : Block c) :
    decode (RootSources.senderWords (RootSources.paddedRow obs.stencil obs.peers obs.marks
      (fun u j=>((ranksAt) u j).val) (fun _=>previousDigit frm.basis fit) quota)
      (fun u j=>(((ranksAt) u j).val:Cell field)) ((large) v) hi)=
      senderSample A S ready digits order Z T frm group name setup v hi:=by
  rw [RootSources.sender_decode]
  apply Prod.ext
  · funext j
    dsimp only [Prod.fst]
    have hq : quota (large v)=peerData (a:=field) A S ready digits Z T frm name v:=
      funext fun j=>funext fun l=>funext fun s=>issued v j l s
    simp only [RootSources.paddedRow,Equiv.symm_apply_apply,hq,desk_window A S ready digits order Z T frm group name pad obs]
    rfl
  · rfl

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
