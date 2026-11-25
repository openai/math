import OAI.Hierarchy.DescentDatedOrdinaryHeld
import OAI.Hierarchy.DescentPreviousOperandLimit

namespace OAI
/-! The seven returned operand pages survive the new primitive archive and both honest counters. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentColonies
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root shelf header : ℕ)
  (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
  {w : ℕ} (s : ResultSteps w) (bank : v.ResultRoom (v.stageStart root) B w) (d : DonorDate) (positive : 0< d.exponent)
local notation "floor" => v.stageStart root
local notation "lay" => d.schedule v.payload v.seats v.bitsPerField
local notation "rot" => (lay).rotationEnd input.roster floor
local notation "measure" => (⟨v.prior.placement.wire,v.prior.placement.z,v.prior.placement.hist⟩:Dated.Measures)
local notation "src" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "meter" => d.counter v.payload rot header
local notation "meterEnd" => (meter).endAddr
local notation "vbase" => v.rasterEnd floor
local notation "ready" => v.metaStart floor
local notation "args" => v.venue.operands B vbase
variable (fit : Room v root shelf header input count wires s d)


open DescentPackedColony DescentOperandStateBanks DescentDatedPriorOperand
local notation "chart" => v.nodeChart
local notation "venue₀" => v.venue.phase B vbase w
local notation "current" m => v.beforeReturn root shelf header input count wires s d positive fit m
local notation "rows₀" => (fun x:Fin (chart).blocks=>v.venue.metadataPaid B x.val)

def beforeArgumentWrite (m : Memory w) : Memory w :=
  (chart).ordinaryImage (v.metaStart floor) v.metadata.paidBits (v.resolver.size+2)
    rows₀ (v.spanVectors floor) ((venue₀).image (current m))

local notation "argEntry" m => v.beforeArgumentWrite root shelf header input count wires B s d positive fit m
local notation "op" => v.argumentsAfter floor bank.operands
  (by rw [v.after_end floor bank.geometry]; exact bank.limit)
local notation "base₀" => v.finalChart.out (v.metaEnd floor)

theorem date_argument_read (m:Memory w) (j:ℕ) (end₀:j<v.operandEnd floor)
    (saved:meterEnd≤j) (away:j≠header) :
    v.dateOutput root shelf header input count wires B s bank d positive fit m j =
      (op).image (argEntry m) j :=by
  let before:=current m
  let written:=(v.returnPhase floor B w bank).image before
  let archived:=s.primitive.image written
  let counted:=(v.counter floor w).image archived
  have pass:=(fit.late.primitive.2 written).2 j (.inl end₀)
  have total:=(v.counter_run floor archived fit.topology fit.limit).2 j (.inl (end₀.trans_le fit.late.primitive.1))
  exact ((meter).counter_frame counted fit.counter j away (.inr saved)).trans (total.trans pass)

theorem date_argument_word (m:Memory w) (x:Fin v.resolver.blocks) (p:Pages v.resolver.operands)
    (r:Fin v.resolver.rows) (saved:meterEnd≤base₀) (away:header< meterEnd) :
    let q:=(previousBank v.resolver base₀ x p).base+r.val
    v.dateOutput root shelf header input count wires B s bank d positive fit m q=(op).image (argEntry m) q :=by
  intro q
  have roof:v.resolver.previousLimit base₀=v.operandEnd floor:=by
    rw [operandEnd,bank.geometry]
    change base₀+(7*v.resolver.operands)*(v.resolver.blocks*v.resolver.rows)+_=base₀+((7*v.resolver.operands)*v.resolver.blocks)*v.resolver.rows+_
    simp only [Nat.mul_assoc,show v.finalChart.rows=v.resolver.rows by rfl]
  have extent:=v.resolver.previous_fit base₀ (v.operandEnd floor) w roof.le bank.limit x p
  let dir:=previousBank v.resolver base₀ x p
  have rowsFit:v.resolver.rows≤dir.size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1<2) _)
  have lo:base₀≤dir.base:=by change _≤base₀+_+_;omega
  have hi:q<v.operandEnd floor:=(Nat.add_lt_add_left (r.isLt.trans_le rowsFit) _).trans_le extent.2.2
  have after:=saved.trans (lo.trans (Nat.le_add_right dir.base r.val))
  exact v.date_argument_read root shelf header input count wires B s bank d positive fit m q hi after
    (ne_of_gt (away.trans_le after))

theorem date_argument_rows (m:Memory w) (x:Fin v.resolver.blocks) (p:Pages v.resolver.operands)
    {b:ℕ} (data:Fin v.resolver.hosts→Fin v.resolver.groups→Cell b)
    (saved:meterEnd≤base₀) (away:header< meterEnd)
    (read:Reads (previousBank v.resolver base₀ x p) data v.resolver.lanes ((op).image (argEntry m))) :
    Reads (previousBank v.resolver base₀ x p) data v.resolver.lanes
      (v.dateOutput root shelf header input count wires B s bank d positive fit m) :=by
  intro t
  exact (v.date_argument_word root shelf header input count wires B s bank d positive fit m x p (row _ _ _ t)
    saved away).trans (read t)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
