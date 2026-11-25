import OAI.Hierarchy.DescentCalendarPrivateMeta
import OAI.Hierarchy.DescentCalendarContactField
import OAI.Hierarchy.DescentCalendarSectorRoutes

namespace OAI
/-! # The reached mixed sheets at their physical compact actor addresses -/
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

local notation "geom₀" => PhysicalReset.DateInputs.SheetGeometry I
local notation "cells₀" => (R₀).capturedChannels
local notation "xfer₀" => I.masked.image (I.privateResult m)
local notation "field" => I.masked.field
local notation "header₀" => DescentResetFieldAssembler.raw field
local notation "area₀" => (s₀).contacts+(s₀).privates
local notation "groupCast" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "blockCast" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck

/-- The concrete calendar gives the number, block and offset of each of the two physical job families. -/
theorem calendar_sheet_geometry (front : (v₀).front=month) (sheets : (v₀).sheets=table₀) : geom₀ := by
  constructor
  · rw [sheets];rfl
  · change (s₀).contacts=DescentContactMaskShape.sockets (phys₀).donor
    rw [front,sheets];rfl
  · change (s₀).privates=2*(rootSlots (phys₀).contact.residual (2^(phys₀).contact.n)*(phys₀).wireCap)
    rw [front,sheets];rfl
  · rfl
  · rfl

local notation:max "site_" groupIx:arg h:arg x:arg => ((((groupIx).cast groupCast,(compactActorOrder B pad).symm h),(x).cast blockCast):host₁)

def contact_meta_at (geo : geom₀) (x : Fin (s₀).blocks) (q : Fin (s₀).contacts) (h : Fin used) (groupIx : Fin I.masked.groups) :=
  let u:=site_ groupIx h x
  let t:=(q.cast geo.contacts).cast (congrArg DescentContactOutputShape.Shape.sockets cal.contactDeck)
  «meta» B u (localOrigin B u (contactShelfIndex B t))

def private_meta_at (geo : geom₀) (x : Fin (s₀).blocks) (q : Fin (s₀).privates) (h : Fin used) (groupIx : Fin I.masked.groups) :=
  let u:=site_ groupIx h x
  let t:=(q.cast geo.privates).cast (congrArg DescentPrivateMaskDeck.Shape.keys cal.privateDeck)
  «meta» B u (localOrigin B u (privateShelfIndex B t))

include paid record four missing origins in
set_option maxHeartbeats 800000 in
theorem measured_sectors (geo : geom₀) (ok : I.Ready) (x : Fin (s₀).blocks)
    (lanes : 0<I.masked.lanes) (rankFit : I.masked.lanes*max (I.masked.field*5) I.masked.field≤bw/2)
    (maskFit : I.masked.lanes*max (I.masked.field*9) (I.masked.field*7)≤bw/2)
    (contacts : ∀(q : Fin (s₀).contacts) (h : Fin used) (g : Fin I.masked.groups),
      DescentCandidateMaskRAM.render ((cells₀).maskValues (R₀).names (x.val*area₀+q.val) (h.castLE seen.used) g)=
        header₀ (contact_meta_at B oldBatch batch calendar I cal pad geo x q h g)) :
    (∀q,DescentPackedZip.Source (I.sectorHeader x.val (.inr (.inr (.inl q))))
      (fun (h : Fin I.masked.hosts) groupIx=>header₀ (if live:h.val<used then contact_meta_at B oldBatch batch calendar I cal pad geo x q ⟨h.val,live⟩ groupIx else DescentResetFieldAssembler.Meta.blank))
      I.masked.lanes xfer₀) ∧
    ∀q,DescentPackedZip.Source (I.sectorHeader x.val (.inr (.inr (.inr q))))
      (fun (h : Fin I.masked.hosts) groupIx=>header₀ (if live:h.val<used then private_meta_at B oldBatch batch calendar I cal pad geo x q ⟨h.val,live⟩ groupIx else DescentResetFieldAssembler.Meta.blank))
      I.masked.lanes xfer₀:=by
  have narrow : I.masked.field≤bw:=by
    have step:=Nat.le_mul_of_pos_left (max (I.masked.field*5) I.masked.field) lanes
    have small:=Nat.le_max_right (I.masked.field*5) I.masked.field
    omega
  refine PhysicalReset.DateInputs.sector_sources (R₀) geo x
    (contact_meta_at B oldBatch batch calendar I cal pad geo x)
    (private_meta_at B oldBatch batch calendar I cal pad geo x) m ok seen
    (measured_private_shapes B oldBatch batch calendar I cal pad prior xs raw near pay trees origins)
    lanes rankFit maskFit contacts ?_
  intro q h groupIx
  let u:=site_ groupIx h x
  let job:=x.val*area₀+((s₀).contacts+q.val)
  have block : u.2.cast (blockCast).symm=x.cast geo.privateBlocks:=Fin.ext rfl
  have routed:=(geo.private_job x q)
  rw [←block] at routed
  have reached:=measured_private_meta B oldBatch batch calendar paid I cal pad prior xs raw near m seen
    record pay trees origins four missing ok u (q.cast geo.privates) job routed narrow
  have actor : (compactActorOrder B pad) u.1.2=h := (compactActorOrder B pad).apply_symm_apply h
  have axis : u.1.1.cast (groupCast).symm=groupIx := Fin.ext rfl
  have address := congrArg₂ (fun (hostId : Fin used) (groupId : Fin I.masked.groups) =>
    DescentCandidateMaskRAM.render ((cells₀).maskValues (R₀).names job (hostId.castLE seen.used) groupId))
    actor axis
  exact address.symm.trans reached

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
