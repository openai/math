import OAI.Hierarchy.DescentCalendarRankValues
import OAI.Hierarchy.DescentContactReachedIndicators

namespace OAI
/-! # Reading each projected contact on its actual compact actor and native group lane -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup
noncomputable section
abbrev CalendarFields (A : DescentContactOutputShape.Shape) :=
  Fin A.sockets→Fin 4→Fin A.sparseHosts→Fin A.donor.groups→Cell A.metaBits

theorem cast_field {A B : DescentContactOutputShape.Shape} (eqn : A=B) (f : CalendarFields B)
    (q : Fin A.sockets) (j : Fin 4) (v : Fin A.sparseHosts) (g : Fin A.donor.groups) :
    ((cast (congrArg CalendarFields eqn.symm) f) q j v g).val=
      (f (q.cast (congrArg DescentContactOutputShape.Shape.sockets eqn)) j
        (v.cast (congrArg DescentContactOutputShape.Shape.sparseHosts eqn))
        (g.cast (congrArg (fun s : DescentContactOutputShape.Shape=>s.donor.groups) eqn))).val:=by
  subst B; rfl

end
end Hierarchy.DescentContactOutputShape.Shape

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
open scoped Classical
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

local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth

/-- The bank at the compact actor gives the donor's measured word on the actual group/block lane. -/
theorem contact_field_at (u : host₁) (q : Fin (K₀).sockets) (j : Fin 4) :
    let x:=u.2.cast (congrArg DescentContactOutputShape.Shape.blocks cal.contactDeck).symm
    let groupId:=u.1.1.cast (congrArg DescentContactOutputShape.Shape.groups cal.contactDeck).symm
    let hostId:=compactActorOrder B pad u.1.2
    let t:=q.cast (congrArg DescentContactOutputShape.Shape.sockets cal.contactDeck)
    (DescentResetDenseOperand.dense («H»:=I.masked.hosts) (R₀).names ((R₀).capturedChannels.contact x q j)
      (hostId.castLE seen.used) groupId).val=
      ((((good).rawIndicators don₀ (Z).graph xs adj_ raw t).indicators.output j
        (named₀ u.1.2) ((digits).symm (u.1.1,u.2))).val) :=by
  intro x groupId hostId t
  rw [(R₀).contact_at m seen hostId groupId x q j]
  have transfer:=DescentContactOutputShape.Shape.cast_field cal.contactDeck
    (trueContactRegisters B oldBatch batch calendar I pad xs raw) q j
    (((R₀).names hostId).cast (R₀).slots) ((finProdFinEquiv (groupId,x)).cast (R₀).coarse.symm)
  refine transfer.trans ?_
  have vEq : ((((R₀).names hostId).cast (R₀).slots).cast (congrArg DescentContactOutputShape.Shape.sparseHosts cal.contactDeck))=
      named₀ u.1.2:=by
    apply Fin.ext
    change (compactActorName B pad (compactActorOrder B pad u.1.2)).val=_
    simp only [compactActorName,Equiv.symm_apply_apply]
  have gEq : (((finProdFinEquiv (groupId,x)).cast (R₀).coarse.symm).cast
      (congrArg (fun layout : DescentContactOutputShape.Shape=>layout.donor.groups) cal.contactDeck))= (digits).symm (u.1.1,u.2):=by
    rw [←original_contact_lane B]
    apply Fin.ext
    simp only [groupId,x,Fin.val_cast,finProdFinEquiv_apply_val]
    change u.2.val+(K₀).blocks*u.1.1.val=u.2.val+2^k*u.1.1.val
    exact congrArg (fun blocks : ℕ => u.2.val+blocks*u.1.1.val)
      (congrArg DescentContactOutputShape.Shape.blocks cal.contactDeck)
  rw [vEq,gEq];rfl


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
