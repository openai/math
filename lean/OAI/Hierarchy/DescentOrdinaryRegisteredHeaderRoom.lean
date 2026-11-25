import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentOrdinaryRegisteredWordRoom

namespace OAI
/-! Both numerical bounds for an ordinary output pointer at the original dated step. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
set_option quotPrecheck false
set_option hygiene false
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root


local notation "model" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

set_option hygiene true
set_option quotPrecheck true
theorem ordinary_header_capacities (dated:i<S.length) (previous:prior.argumentsPerNode≤S.retainedArgumentsAt G drift) :
    next.placement.cap≤2^(model).finalChart.field ∧ (model).finalChart.keys≤2^(model).finalChart.field :=by
  have width:(model).finalChart.field=DescentOperandWidth.recordBits G S k tail drift degree p:=
    (OrdinaryBooks.record_width G S op gain k i p tail drift degree payload seats prior).1
  rw [width]
  have grows : 2^(8+S.capGain*(i+1))≤DescentOperandWidth.publicCap S :=
    Nat.pow_le_pow_right (by decide) (by apply Nat.add_le_add_left;exact Nat.mul_le_mul_left _ dated)
  have public_bound : DescentOperandWidth.publicCap S≤DescentOperandWidth.raw S :=by
    dsimp [DescentOperandWidth.raw];omega
  have scalar : DescentOperandWidth.s G S k tail drift degree ≤DescentOperandWidth.recordBits G S k tail drift degree p :=
    Nat.le_max_left ..
  have cutoff {n:ℕ} (small : n≤DescentOperandWidth.bound G S drift degree) :
      n≤2^(DescentOperandWidth.recordBits G S k tail drift degree p) :=
    (DescentOperandWidth.numeric G S (k:=k) (tail:=tail) small).le.trans
      (Nat.pow_le_pow_right (by decide) scalar)
  refine ⟨cutoff (next.valid.capacity.trans (grows.trans (public_bound.trans
    ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))))),?_⟩
  have rectangle:(model).finalChart.keys=NativeBranch.privateSlotCapacity G S drift :=by
    change S.retainedNodes*(max prior.argumentsPerNode (S.retainedArgumentsAt G drift))=_
    rw [max_eq_right previous]
    simp only [AtomSchedule.retainedNodes,AtomSchedule.retainedArgumentsAt,
      AtomSchedule.retainedArguments,NativeBranch.privateSlotCapacity,pow_add]
    ac_rfl
  rw [rectangle]
  exact cutoff ((Nat.le_max_left ..).trans (Nat.le_max_left ..))

/-- Every real flattened arity fits the scalar word on the registered metadata page. -/
theorem ordinary_header_arity_width (previous:prior.argumentsPerNode≤S.retainedArgumentsAt G drift) :
    (model).resolver.operands<2^(model).finalChart.field :=by
  have width:(model).finalChart.field=DescentOperandWidth.recordBits G S k tail drift degree p:=
    (OrdinaryBooks.record_width G S op gain k i p tail drift degree payload seats prior).1
  rw [width]
  change max prior.argumentsPerNode (S.retainedArgumentsAt G drift)<_
  rw [max_eq_right previous]
  exact DescentOperandWidth.registered_arguments G S k tail drift degree p

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
