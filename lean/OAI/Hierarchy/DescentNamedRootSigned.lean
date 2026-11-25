import OAI.Hierarchy.DescentNamedOriginalHeader

namespace OAI
/-! The named reset's measured root receiver reads the original signed venue and saved rotation. -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots
open ProtocolRAM
variable {D cap N n r c H G K R M hm lb tiny field Ht w D' cap' n' r' c' H' G' Ht' : ℕ}

theorem reindex_input_addresses (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
    (d : D=D') (cp : cap=cap') (nn : n=n') (rr : r=r') (cc : c=c')
    (hh : H=H') (gg : G=G') (ht : Ht=Ht') (addr : ℕ→ℕ→Bank)
    (inputs : ∀j k,x.receiver.old j k=addr k.val j.val) :
    let next:=x.reindex d cp nn rr cc hh gg ht
    next.receiver.saved=x.receiver.saved ∧ ∀j k,next.receiver.old j k=addr k.val j.val :=by
  subst D'; subst cap'; subst n'; subst r'; subst c'; subst H'; subst G'; subst Ht'
  exact ⟨rfl,inputs⟩
end Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl}
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "successor₀" => (a).successor
local notation "start" => (a).stageStart floor
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w

variable (prepared : (rc).PreparedFits book)
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "HH" => S.hostSize age

open DescentFallbackPeriod.Projected
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)

open DescentGL DescentPacking.PackedMatch.Local
local notation "staged" => fromNamed_matrix_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt

private theorem cast_matrix_word {d₀ d₁ : ℕ} (eqn : d₀=d₁) (μ : DescentGL.Layout d₀) :
    (DescentExterior.matrixCode (cast (congrArg DescentGL.Layout eqn) μ)).val=(DescentExterior.matrixCode μ).val :=by
  cases eqn
  rfl

theorem DateInputs.fromNamed_root_signed (mem measured : Memory w) (μ : DescentGL.Layout (E).dim)
    (saved : measured (P).saved=((DescentExterior.matrixCode μ).val:Word w))
    (kept : ∀addr < floor,measured addr=mem addr)
    (seen : stageVenue input input.valid.host io (successor₀).funded.oldLanes (successor₀).funded.precision floor
      (input.venueRoster input.valid.host) mem)
    (wireRoom : ∀(x : DescentColonies.Block k)(j : Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (successor₀).funded.oldLanes ≤ (io.wire x.val j.val).size)
    (pitch : venue.lanes=2^previous) (dim : (E).dim=cc-e+(e+k)) :
    (∀(j : Fin (2*input.placement.cap)) (x : DescentColonies.Block k), Reads ((staged).receiver.old j x) (fun h g=>
      DescentSignedCableCodec.encode (Stage.Prepare.signed input.placement (input.order.trans Fin.valEmbedding)
        S input.valid (Equiv.refl (Fin (S.groupCount age))).toEmbedding idx x j h g)) (2^(previous-e)*2^e) measured) ∧
      measured (staged).receiver.saved.base =
        ((DescentExterior.matrixCode (cast (congrArg DescentGL.Layout dim) μ)).val:Word w) :=by
  have bank : (staged).receiver.saved=(rc).saved ∧
      ∀j x,(staged).receiver.old j x=io.wire x.val j.val :=by
    unfold fromNamed_matrix_image
    apply Receiver.IndexedRoots.reindex_input_addresses
    exact fun _ _=>rfl
  constructor
  · intro j x
    have lanesEq : 2^(previous-e)*2^e=venue.lanes := by rw [←pow_add, Nat.sub_add_cancel fitsSigned, pitch]
    rw [bank.2 j x, lanesEq]
    intro row₀
    have small := (row HH (S.groupCount age) venue.lanes row₀).isLt.trans_le (wireRoom x j).2
    rw [kept _ ((Nat.add_lt_add_left small _).trans_le (wireRoom x j).1.2.2)]
    exact seen.2.2.2.1 x j row₀
  · rw [bank.1]
    exact saved.trans (congrArg (fun j : ℕ => (j : Word w)) (cast_matrix_word dim μ).symm)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
