import OAI.Hierarchy.DescentOrdinaryRegisteredHeaderRoom
import OAI.Hierarchy.DescentPhysicalSignedLayout
import OAI.Hierarchy.DescentMaximumDegreeQuota
import OAI.Hierarchy.DescentSenderBoardHeight
import OAI.Hierarchy.DescentDatedMaterialPhase
import OAI.Hierarchy.DescentDatedMeter
import OAI.Hierarchy.DescentOrdinaryShapeSlots

namespace OAI
/-! Operand and signed-cable field bounds for the original registered ordinary date. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentSixParty.Chronology DescentCompiler DescentDatedAddressBook
open DescentPacking.PackedMatch.Local.Stage DescentHaloWalkRAM
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prior : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {nrm : Normalize ((T.result he).state choice)}
    {next : Reached nrm.result G q ε S k (i+1) z' D' wire hist}
    (ports : DatePorts) (ticket : OrdinaryLink prior he T choice nrm next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "model" => DatePorts.ordinaryModel ports ticket op gain tail p f drift degree payload seats root ordinary
local notation "phys" => (model).withIssuedSigned
local notation "field" => ((phys).resolver.size+2)
local notation "roundCap" => maximumDegree (S.rounds+1)

/-- Both degrees come from the same recorded ordinary round and its successor. -/
theorem cut_numeric_header_bounds
    (previous : ports.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (walks : breadth roundCap ≤ 2^k) :
    breadth prior.placement.degree*2^k ≤ 2^field ∧ 11*prior.placement.cap ≤ 2^field ∧
    (phys).resolver.operands ≤ 2^field ∧ 11 ≤ 2^(phys).bornBook.bits ∧
    next.placement.cap ≤ 2^(phys).signed.fieldBits ∧ next.placement.degree ≤ 2^(phys).signed.fieldBits ∧
    next.placement.cap ≤ 2^field ∧ next.placement.degree ≤ 2^field := by
  classical
  have dated : i<S.length := ticket.hubRows.choose
  obtain ⟨j, hj, phase⟩ := ticket.degreeSlot
  have within (m : ℕ) (fits : m<S.rounds+1) : atRound m≤roundCap :=
    Finset.single_le_sum (f:=fun a : Fin (S.rounds+1) => atRound a.val)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨m,fits⟩ : Fin (S.rounds+1)))
  have old : prior.placement.degree≤roundCap := by
    rw [prior.branch,phase]
    exact within j (by omega)
  have newDegree : next.placement.degree≤roundCap := by
    rw [next.branch,ticket.nextDegree,phase]
    exact within (j+1) (by omega)
  have halo : breadth prior.placement.degree≤2^k :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right old 1) 4).trans walks
  have words := OrdinaryBooks.record_width G S op gain k i p tail drift degree payload seats ports
  have width : field=DescentOperandWidth.recordBits G S k tail drift degree p := words.1
  have mouth : (phys).bornBook.bits=field :=words.2.2.1
  have scalar : DescentOperandWidth.s G S k tail drift degree ≤ field :=by
    rw [width]
    exact Nat.le_max_left ..
  have stamp : S.stampBits k tail ≤ DescentOperandWidth.s G S k tail drift degree :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have depth : 1≤S.length := by omega
  have kd := Nat.mul_le_mul_left k depth
  simp only [Nat.mul_one] at kd
  have doubled : k+k ≤ S.stampBits k tail := by
    change k+k≤tail+k*(S.length-0)+k
    simp only [Nat.sub_zero]
    omega
  have rank : breadth prior.placement.degree*2^k ≤ 2^field :=
    calc _ ≤ 2^k*2^k := Nat.mul_le_mul_right _ halo
         _ = 2^(k+k) := (pow_add ..).symm
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (doubled.trans (stamp.trans scalar))
  have raw := DescentOperandWidth.cableName G S (k:=k) (tail:=tail) (drift:=drift)
    (degree:=degree) (role:=0) dated.le prior.valid.capacity (by decide)
  have name : 11*prior.placement.cap ≤ 2^field :=
    (show 11*prior.placement.cap ≤ 2^(DescentOperandWidth.s G S k tail drift degree) by
      simpa only [Nat.add_zero] using raw.le).trans (Nat.pow_le_pow_right (by decide) scalar)
  have small : 11≤DescentOperandWidth.raw S :=by dsimp [DescentOperandWidth.raw];omega
  have mouthFit : 11≤2^(phys).bornBook.bits :=by
    rw [mouth]
    apply le_trans _ (Nat.pow_le_pow_right (by decide) scalar)
    exact (DescentOperandWidth.numeric G S (k:=k) (tail:=tail) (drift:=drift) (degree:=degree)
      (small.trans ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))))).le
  have signed : max (next.placement.degree+1) (next.placement.cap+1)<2^(phys).signed.fieldBits :=
    (model).signedLayout.field_room.2.1
  have peer : roundCap≤breadth roundCap :=by
    have grow:=Nat.pow_le_pow_right (Nat.succ_pos roundCap) (show 1≤4 by decide)
    simp only [pow_one] at grow
    exact (Nat.le_succ _).trans grow
  have base : k≤field :=(Nat.le_add_left _ _).trans (doubled.trans (stamp.trans scalar))
  exact ⟨rank,name,(DatePorts.ordinary_header_arity_width ports ticket op gain tail p f
    drift degree payload seats root ordinary previous).le,mouthFit,by omega,by omega,
    (DatePorts.ordinary_header_capacities ports ticket op gain tail p f drift degree payload seats
      root ordinary dated previous).1,
    newDegree.trans (peer.trans (walks.trans (Nat.pow_le_pow_right (by decide) base)))⟩

/-- The preceding operand page has at least two tag bits when its recorded width
agrees with the registered resolver. The node-count word includes its zero case. -/
theorem cut_numeric_counts (width : field=ports.operandBits) :
    2≤ports.operandBits ∧ ports.nodes<2^(model).reference.countBits := by
  constructor
  · rw [←width]
    omega
  · exact (Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _)

/-- The material depot uses the ticket's actual fan-out and original block chart. -/
theorem cut_numeric_material_axes :
    (phys).materialPitch=(2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots prior.placement.degree ∧
    (phys).material.blocks=2^k := by
  constructor
  · change (2^(k+1)-1)*(2^DescentHostDegree.packExponent 20 T.Δ+2)=_
    rw [(Dated.Meter.ticket_shape ticket).2]; rfl
  · rfl

open Filter DescentCompiler.TerminalScale in
/-- One height cutoff supplies the walk reservation at every ordinary date. -/
theorem cut_numeric_walks (rounds B host gain cut : ℕ) (positive : 0<B) :
    ∀ᶠ h : ℕ in atTop,
      breadth (maximumDegree (rounds+1)) ≤ 2^groupBits rounds (Nat.log 2 h/(2*B)) host gain cut :=
  DescentDatedAddressBook.ResetMiddle.sender_board_at rounds B host gain cut _ positive

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
