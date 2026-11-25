import OAI.Hierarchy.DescentDatedArchiveWidths
import OAI.Hierarchy.DescentInitialArgumentCapacity

namespace OAI
/-! # Every actual predecessor register fits the common retained argument multiplicity -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentDatedAddressBook DescentDatedSeedStartup DescentPacking.PackedMatch.Local.Stage
open DescentPrimitivePalette DescentDatedOperandReadPipeline ProtocolRAM
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec)


def ArgumentSlots (prior : DatePorts) (drift : ℕ) : Prop := prior.argumentsPerNode ≤ S.retainedArgumentsAt G drift

theorem seed_argument_slots {c nP p : ℕ} (X : Catalyst.Approximation F c nP) (R h k tail gain drift degree f quota base field wire hist H groups : ℕ)
    (late : 0<S.height) (branch : G.b≤2^S.capGain) :
    let l:=selectedLayout G S h k tail gain p drift degree f quota base field wire hist
    ArgumentSlots G S (initial G op X R l k H groups h (S.grainAt G.b p 0)) drift :=
  S.seed_argument_capacity G p drift late branch

section Ordinary
variable {P : Type} {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (gain tail p f drift degree h seats root : ℕ) (ordinary : ℕ→Dated.Ordinary)

theorem ordinary_argument_slots (held : ArgumentSlots G S prior drift) :
    ArgumentSlots G S (ordinaryPorts prior ticket op gain tail p f drift degree h seats root ordinary) drift :=
  max_le held le_rfl

end Ordinary

section Reset
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (oldOperand oldPrimitive : ℕ) (old : StageVenueTail.Date)
    (wire : ℕ→ℕ→Bank) (roster : Bank) (floor : ℕ)
local notation "tag" => printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "a" => PhysicalReset.scheduled G S board k tail age p f g drift degree h ordinary op
  (S.firstWidth G.b p) (S.grainAt G.b p 0) oldOperand oldPrimitive old wire roster floor


theorem reset_argument_slots {w : ℕ} (inputs : (a).DateInputs ((a).stageStart floor) w) :
    ArgumentSlots G S (reset (a) ((a).stageStart floor) inputs) drift :=le_rfl

end Reset

theorem ArchiveWidths.node_bound {ports : DatePorts} {k tail p drift degree h age : ℕ}
    (receipt : ArchiveWidths G S op ports k tail p drift degree h age) : ports.nodes≤S.retainedNodes :=by
  rw [receipt.nodes]
  split
  · exact (Nat.pow_pos (Nat.pow_pos (by decide : 0<(2:ℕ))))
  · exact le_rfl

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
