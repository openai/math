import OAI.Hierarchy.DescentObservedContactMask
import OAI.Hierarchy.DescentCalendarContactField
import OAI.Hierarchy.DescentCalendarSenderProbes

namespace OAI
/-! # Actual contact fields and ranks on the common receiver calendar -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

local notation "R₀" => measured_menu B oldBatch batch calendar I cal pad prior xs raw near
local notation "host₁" => DescentSharedCableNames.Stage.Host (Fin gs) B.next.V k
local notation "named₀" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))
local notation "s₀" => (v₀).sheets


local notation "regs₀" => (v₀).jointRegisters base₀ I.earlier
local notation "real₀" => compactActorName B pad
local notation "rows₀" => DescentResetPeerUnionRAM.selfPeers near
variable (m : Computability.VPVNP.BurstRAM.Memory bw) (seen : PhysicalReset.DateInputs.CaptureRoom (R₀) m)



open DescentIssuedFallbackPanel DescentOldContactSender DescentSharedCableNames
local notation "natOrder" => input.order.trans Fin.valEmbedding
local notation "gr" => Function.Embedding.refl (Fin (S.groupCount i))
local notation "wireNames" => cableNames k (DescentStageEdgeReceipt.groupRank ((gr).trans Fin.valEmbedding) ((portChart).trans Fin.valEmbedding))
local notation "oldDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "inside" => B.frame.enough.trans (Nat.sub_le ..)
local notation "query" => Nat.clog 2 (D+2)
local notation "cargo" => Nat.clog 2 (D+3)
local notation "width" => (month).contact.outputBits

/-- The previous root observation and the original signed grain words. These
are the first two conclusions of the single measured sender transaction. -/
structure ContactSenderRead : Prop where
  original : ∃setup : (senderDesk B field₀).Inputs,∀v l,decode (xs (portChart v) l)=(senderDesk B field₀).sample setup v l
  signed : ∀v l lo j,raw lo j (portChart v) l=DescentResetOppositePayload.widened (A).degree (A).cap field₀
    (Stage.signedPanel (A) natOrder S input.valid wireNames (donor oldDigits B.frame.basis inside v l lo) j)

structure ContactFieldRoom : Prop where
  originalCount : L*K<2^field₀
  originalShapes : shelf≤2^field₀
  keys : rootSlots r (2^(Z).n)*(2^(Z).n+2^ht)<2^field₀
  marker : (A).degree*shelf<2^width
  signed : DescentSignedCableCodec.width (A).degree (A).cap≤field₀
  port : (A).degree+1<2^query
  opposite : (A).degree+2<2^cargo

variable {p : ℕ} (record : B.Recorded p)
    (four : ∀v : B.next.V,present rows₀ (named₀ v)=(insert v ((Z).emittedNear T v)).map named₀)
    (missing : ∀v : B.next.V,(∀j,near (named₀ v) j≠some (named₀ v)) ↔ v∉(Z).emittedNear T v)

include paid record four missing in
set_option maxHeartbeats 800000 in
theorem measured_contact_meta (sender : ContactSenderRead B calendar pad xs raw)
    (room : ContactFieldRoom B oldBatch batch calendar) (ok : I.Ready) (u : host₁)
    (q : Fin (K₀).sockets) (job : ℕ)
    (routed : (v₀).jobAt job=some (.inl (u.2.cast (congrArg DescentContactOutputShape.Shape.blocks cal.contactDeck).symm,q)))
    (narrow : I.masked.field≤bw) :
    let groupIx:=u.1.1.cast (congrArg DescentContactOutputShape.Shape.groups cal.contactDeck).symm
    let actor:=(compactActorOrder B pad u.1.2).castLE seen.used
    let t:=q.cast (congrArg DescentContactOutputShape.Shape.sockets cal.contactDeck)
    DescentCandidateMaskRAM.render ((R₀).capturedChannels.maskValues (R₀).names job actor groupIx)=
      DescentResetFieldAssembler.raw I.masked.field («meta» B u (localOrigin B u (contactShelfIndex B t))) := by
  intro groupIx actor t
  obtain ⟨setup,measured⟩:=sender.original
  have fieldEq : meta₀=I.masked.field:=(congrArg DescentContactOutputShape.Shape.metaBits cal.contactDeck).symm
  have amount : max 5 (2^g*(calendar.take i).prod*256+2) ≤ 2^I.masked.field:=by
    change _≤2^(v₀).sheets.metaBits
    rw [cal.fieldWidth]
    unfold CandidateFront.endpointWidth
    have combine : 2^g*(calendar.take i).prod*256=2^g*cap:=by simp only [Nat.mul_assoc]
    rw [combine]
    exact (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))
  have mass : B.next.placement.cap<2^meta₀:=by
    rw [fieldEq,B.next_capacity,paid]
    have h:=Nat.le_max_right 5 (2^g*cap+2)
    rw [Nat.mul_assoc] at amount
    omega
  have fourFit : 4≤2^I.masked.field:=(by omega : 4≤ max 5 (2^g*(calendar.take i).prod*256+2)).trans amount
  have coord : shelf*DescentResetPeerJointRAM.radix (A).degree≤2^I.masked.field:=by
    simpa only [cal.peerShapes,cal.oldDegree] using seen.keys
  have join : shelf*DescentResetPeerJointRAM.radix (A).degree≤2^bw:=
    coord.trans (Nat.pow_le_pow_right (by decide) narrow)
  have ports (v : input.V) (j : Fin (A).degree) :
      adj_ (portChart v) j=(hostRoster (A) (input.vertex.trans Fin.valEmbedding) v j).map portChart:=by
    have hit : ∃u,portChart u=portChart v:=⟨v,rfl⟩
    rw [hostRotor,dite_eq_left hit,(portChart).injective hit.choose_spec]
    rfl
  have pos : 0<field₀:=by unfold ResetMiddle.fieldWidth;omega
  have ranks:=measured_rank_values B oldBatch batch calendar I cal pad prior xs raw near m seen actor groupIx
  apply observed_present_word B H oldBatch field₀ query cargo don₀ width pad xs adj_ raw setup measured ports sender.signed room.signed pos
    batch meta₀ room.keys room.opposite (by rw [fieldEq]; exact coord)
    seen.used (R₀).capturedChannels (R₀).names ((v₀).massEnd base₀) regs₀ (I.contactResult m) rows₀
    (measured_rank_limits B oldBatch batch calendar I cal ok)
    (measured_rank_registers B oldBatch batch calendar I cal pad prior xs raw near m seen) join fourFit
    room.originalCount mass room.originalShapes room.marker room.port u.1.2 u.1.1 u.2 t job _ q actor groupIx routed
    (contact_field_at B oldBatch batch calendar I cal pad prior xs raw near m seen u q)
    (by rw [rendered_near B record]; exact four u.1.2) (fun j=>(ranks j).1)
    near (ranks 2).2 (by rw [rendered_near B record]; exact missing u.1.2) fieldEq

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
