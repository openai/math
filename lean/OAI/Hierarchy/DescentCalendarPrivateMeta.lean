import OAI.Hierarchy.DescentCalendarRankValues
import OAI.Hierarchy.DescentPhysicalPrivateMeta
import OAI.Hierarchy.DescentResetWindowEmittedSources

namespace OAI
/-! # Numeric private reset fields at each reached compact actor -/
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



variable {p zsize : ℕ} (record : B.Recorded p) (pay : 0<(Z).unit)
    (trees : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel ht zsize) (origins : PeerOrigins B pad prior pay trees)
    (four : ∀v : B.next.V,present rows₀ (named₀ v)=(insert v ((Z).emittedNear T v)).map named₀)
    (missing : ∀v : B.next.V,(∀j,near (named₀ v) j≠some (named₀ v)) ↔ v∉(Z).emittedNear T v)

include paid record four missing origins in
set_option maxHeartbeats 800000 in
/-- A live compact actor reads precisely the original ordered private menu, on each job,
including a ticket outside the fixed root embedding. -/
theorem measured_private_meta (ok : I.Ready) (u : host₁) (q : Fin (Q₀).keys) (job : ℕ)
    (routed : (v₀).jobAt job=some (.inr (u.2.cast (congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck).symm,q)))
    (narrow : I.masked.field≤bw) :
    let groupIx:=u.1.1.cast (congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck).symm
    let actor:=(compactActorOrder B pad u.1.2).castLE seen.used
    let slot:=q.cast (congrArg DescentPrivateMaskDeck.Shape.keys cal.privateDeck)
    DescentCandidateMaskRAM.render ((R₀).capturedChannels.maskValues (R₀).names job actor groupIx)=
      DescentResetFieldAssembler.raw I.masked.field («meta» B u (localOrigin B u (privateShelfIndex B slot))) :=by
  intro groupIx actor slot
  let x:=u.2.cast (congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck).symm
  let field:=I.masked.field
  let cells:=(R₀).capturedChannels
  let key:=localPrivateId r (2^(Z).n) cap₀
  have amount : max 5 (2^g*(calendar.take i).prod*256+2) ≤ 2^field:=by
    change _≤2^(v₀).sheets.metaBits
    rw [cal.fieldWidth]
    unfold CandidateFront.endpointWidth
    have combine : 2^g*(calendar.take i).prod*256=2^g*cap:=by simp only [Nat.mul_assoc]
    rw [combine]
    exact (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))
  have mass : B.next.placement.cap<2^field:=by
    rw [B.next_capacity,paid]
    have h:=Nat.le_max_right 5 (2^g*cap+2)
    rw [Nat.mul_assoc] at amount
    omega
  have fourFit : 4≤2^field:=(by omega : 4≤ max 5 (2^g*(calendar.take i).prod*256+2)).trans amount
  have fit : shelf*DescentResetPeerJointRAM.radix (A).degree≤2^field:=by
    simpa only [cal.peerShapes,cal.oldDegree] using seen.keys
  have area : shelf≤2^field:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans fit
  have join : shelf*DescentResetPeerJointRAM.radix (A).degree≤2^bw:=fit.trans (Nat.pow_le_pow_right (by decide) narrow)
  have rooted (j : Fin 3) :
      (DescentResetDenseOperand.dense («H»:=I.masked.hosts) (R₀).names (cells.privateFields x q j) actor groupIx).val=
      (privateCandidate B pad prior oldBatch batch meta₀ u slot j).val :=by
    have lt : actor.val<used:=(compactActorOrder B pad u.1.2).isLt
    unfold DescentResetDenseOperand.dense
    rw [dite_eq_left lt]
    exact private_field_at B oldBatch batch calendar I cal pad prior xs raw near u q j
  by_cases present : ∃y,key y=slot
  · let y:=present.choose
    have chosen : key y=slot:=present.choose_spec
    have digit (j : Fin 3) :
        (DescentResetDenseOperand.dense («H»:=I.masked.hosts) (R₀).names (cells.privateFields x q j) actor groupIx).val=
        (privateDigit B pad prior oldBatch batch I.masked.field u y.1 y.2.1 y.2.2 j).val:=by
      have width : I.masked.field=meta₀:=congrArg DescentPrivateMaskDeck.Shape.metaBits cal.privateDeck
      calc
        _=(privateCandidate B pad prior oldBatch batch meta₀ u slot j).val:=rooted j
        _=_:=by rw [width];unfold privateCandidate;rw [dite_eq_left present]
    have ranks:=measured_rank_values B oldBatch batch calendar I cal pad prior xs raw near m seen actor groupIx
    rw [←chosen]
    exact private_present_word B pad seen.used cells (R₀).names ((v₀).massEnd base₀) regs₀ (I.contactResult m)
      rows₀ (measured_rank_limits B oldBatch batch calendar I cal ok)
      (measured_rank_registers B oldBatch batch calendar I cal pad prior xs raw near m seen) join fourFit u actor groupIx
      (by rw [rendered_near B record];exact four u.1.2) (fun j=>(ranks j).1)
      prior pay trees origins oldBatch batch job x q routed y.1 y.2.1 y.2.2 area mass fit cal.oldDegree digit near
      (fun j=>(ranks j).2) (by rw [rendered_near B record];exact missing u.1.2)
  · apply private_gap B u slot
    · exact fun y hy=>present ⟨y,hy⟩
    · change (cells.work (R₀).names job actor groupIx).val=0
      have width:=rooted 2
      unfold PhysicalReset.DateInputs.CandidateChannels.work
      rw [routed]
      refine width.trans ?_
      unfold privateCandidate
      rw [dite_eq_right present]
      rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
