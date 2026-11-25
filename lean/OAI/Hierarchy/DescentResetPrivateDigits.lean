import OAI.Hierarchy.DescentPrivatePeerSupport

namespace OAI
/-! # Exact machine value of a private peer ticket -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


local notation "pool" => DescentDenseHostOrder.roster (Z).graph ((Z).k-(T).commonDepth) height

open DescentResetPeerUnionRAM

/-- Both endpoint digits come from the selected chronological device when the
presence bit is set. The issued ticket consequently fits its physical word. -/
theorem private_word_val {D₀ count field outBits : ℕ} (here : Fin (pool).card)
    (old : Fin (Fintype.card input.V)) (block : Block (T).commonDepth)
    (s : Bool) (ticket : (Z).RootTicket T) (slot : Fin capacity)
    (page : DescentSIMDLookup.Cell (field*(capacity*5)))
    (unit : 0<(Z).unit) (panel : (Z).Fallback→DescentPackedFallbackTree.Panel height count)
    (numbers : PrivateEvidence.frame field capacity slot page =
      DescentPackedPrivateMenu.values (Z).graph ((Z).k-(T).commonDepth) height count (Z).layerBits C (Z).width s slot.val
        ((Z).rootsOf T vertexCode unit s panel ticket old block))
    (installed : ∀p : PrivateOccurrence B,privateRawAt B old block s ticket slot p →
      (Z).expand T vertexCode p.1.2 (PrivateEvidence.frame field capacity slot page)=
        (Z).actualRecord T vertexCode (privateWire B p))
    (room : (D₀+1)*(pool).card<2^outBits) :
    (PrivateEvidence.word D₀ (pool).card field capacity outBits here slot page).val =
      PrivateEvidence.ticket D₀ (pool).card here.val (PrivateEvidence.frame field capacity slot page) := by
  let raw:=PrivateEvidence.frame field capacity slot page
  obtain ⟨flag,_,coord⟩:=private_raw_presence B unit s ticket old block slot panel raw numbers installed
  change ((PrivateEvidence.ticket D₀ (pool).card here.val raw : DescentSIMDLookup.Cell outBits)).val=_
  apply Fin.val_cast_of_lt
  by_cases active : raw 0=1
  · obtain ⟨p,hit⟩:=flag.1 active
    obtain ⟨src,dst⟩:=coord p hit
    have left : raw 1<(pool).card:=src.trans_lt ((Z).hostFields T vertexCode ((blocks B).src (privateWire B p)).1.2).2.isLt
    have right : raw 2<(pool).card:=dst.trans_lt ((Z).hostFields T vertexCode ((blocks B).dst (privateWire B p)).1.2).2.isLt
    rw [Nat.succ_mul] at room
    simp only [PrivateEvidence.ticket,ite_eq_left active]
    split
    · omega
    · split <;> omega
  · simp only [PrivateEvidence.ticket,ite_eq_right active]
    exact Nat.two_pow_pos _

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
