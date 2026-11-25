import OAI.Hierarchy.DescentNamedStemSector
import OAI.Hierarchy.DescentReachedCalendarTrunk

namespace OAI
/-! # The trunk header in the paired rank sheet -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDatedAddressBook DescentSIMDLookup DescentPackedColony
open DescentResetFieldAssembler DescentResetCandidatePair DescentPackedZip ProtocolRAM
open scoped Classical
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "used" => Fintype.card B.next.V
local notation "oldRank" => B.frame.host.symm.toEmbedding.trans input.vertex

theorem shaped_trunk {X X' s s' c c' p p' : ℕ} (hx:X=X') (hs:s=s') (hc:c=c') (hp:p=p')
    (src : Inputs X s c p) (x : Fin X') :
    shaped hx hs hc hp src x (.inr (.inl 0))=src (x.cast hx.symm) (.inr (.inl 0)) := by
  subst X';subst s';subst c';subst p';rfl

variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "s₀" => (v₀).sheets
local notation "pos" => CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
local notation "trunkWordAt" x:arg => (v₀).front.trunkOperand ((v₀).actorEnd base₀) x

/-- The issued trunk field has the rank chart’s actual compact host and unique trunk position. -/
theorem named_trunk_sector {hosts : ℕ} (pad : Fintype.card input.V≤hosts) (bound : used≤(s₀).hosts)
    (hx : (v₀).receiver.blocks=2^k) (hs : I.sectors.stems=stemsCount B)
    (hc : I.sectors.contacts=contactCount B) (hp : I.sectors.privates=privateCount B)
    (state : Computability.VPVNP.BurstRAM.Memory bw)
    (seen : ∀(x : Fin (2^k)),
      (trunkWordAt x.val).Fits bw ((v₀).trunkEnd base₀) ∧
      Source (trunkWordAt x.val) (fun (r : Fin (s₀).hosts) g₀=>
        DescentResetFieldAssembler.raw (s₀).metaBits (actualMeta B (originalTrunkRack B) x (trunkCandidate B) r g₀)) (s₀).lanes state) :
    ∀(x : Fin (2^k)),
      (shaped hx hs hc hp I.sectors.header x (.inr (.inl 0))).Fits bw ((v₀).trunkEnd base₀) ∧
      Source (shaped hx hs hc hp I.sectors.header x (.inr (.inl 0))) (fun r g₀=>
        DescentResetFieldAssembler.raw (s₀).metaBits (actualMeta B
          (rackOf B (((Z).denseHostRank T ((oldRank).trans (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)))
          x (pos (.inr (.inl 0))) r g₀)) (s₀).lanes state := by
  intro x
  have address : shaped hx hs hc hp I.sectors.header x (.inr (.inl 0))=trunkWordAt x.val := by
    rw [shaped_trunk]
    rfl
  have index : pos (.inr (.inl 0))=trunkCandidate B:=Fin.ext (CandidateSheet.trunk_val _ _ _)
  rw [address,index,rack_of_original B pad bound]
  exact seen x

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
