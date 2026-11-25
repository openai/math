import OAI.Hierarchy.DescentDatedPreviousPagesBeforeWrite
import OAI.Hierarchy.DescentDatedOperandNativePreparation
import OAI.Hierarchy.DescentOrdinaryMountedInlet

namespace OAI
/-! The normalized ordinary resolver words survive the paid raster, venue return and metadata writer. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup
open DescentPackedColony DescentOperandStateBanks DescentOperandVectorArena DescentDatedPriorOperand
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F]

/-- The inlet carries seven numerical fields. Relabel its phantom physical-model parameter. -/
def ArgumentEntry.samePorts {v : PhysicalOrdinary F P} (A : v.ArgumentEntry)
    (u : PhysicalOrdinary F P) : u.ArgumentEntry :=
  ⟨A.clip,A.venue,A.previous,A.previousBase,A.rolePitch,A.roleBits,A.role⟩

/-- Equality of the actual issued resolver memories on equal signed models. In particular all
expressions, the original chart, the seven inlet fields and the mounted private tape are kept. -/
theorem mounted_resolver_image {v u : PhysicalOrdinary F P} (fixed : u=v) (floor w : ℕ)
    (A : v.ArgumentEntry) (c : v.SignedChart) (cu : u.SignedChart)
    (mv : A.Match v floor) (mu : (A.samePorts u).Match u floor)
    (sv : v.VectorShape) (su : u.VectorShape)
    (bv : v.resolver.blocks=v.material.blocks) (bu : u.resolver.blocks=u.material.blocks)
    (pv : 0<v.vector.operands) (pu : 0<u.vector.operands)
    (fv : v.endAddress floor<2^w) (fu : u.endAddress floor<2^w)
    (wv : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (wu : u.resolver.lanes*DescentPackedOperand.unit u.resolver.size≤w/2)
    (input output : Memory w) (memory : input=output) :
    let E:=A.samePorts u
    let pgu : Fin (7*u.vector.operands):=⟨0,Nat.mul_pos (by decide) pu⟩
    let pgv : Fin (7*v.vector.operands):=⟨0,Nat.mul_pos (by decide) pv⟩
    (u.routedArguments floor (E.directory u floor mu).refs (u.nativeTicketExpr floor cu E mu su bu)
      (u.nativeTicketPreparation floor w cu E mu su bu pgu) su fu wu).image (E.mountedTape u floor input)=
    (v.routedArguments floor (A.directory v floor mv).refs (v.nativeTicketExpr floor c A mv sv bv)
      (v.nativeTicketPreparation floor w c A mv sv bv pgv) sv fv wv).image (A.mountedTape v floor output) :=by
  subst u
  subst output
  rfl

variable (v : PhysicalOrdinary F P) (root shelf header : ℕ) (input : Dated.Operands)
    (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
    {w a : ℕ} (s : ResultSteps w) (bank : v.ResultRoom (v.stageStart root) B w)
    (d : DonorDate) (positive : 0<d.exponent) (fit : Room v root shelf header input count wires s d)
local notation "floor₀" => v.stageStart root

include bank in
/-- Whole physical rows, including the padding lanes, on the actual writer input. -/
theorem resolver_words_before_write (m : Memory w)
    (values : Fin v.resolver.jobs→Fin v.resolver.hosts→Fin v.resolver.groups→Cell a)
    (issued : ∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor₀) j) (values j) v.resolver.lanes
      (s.arguments.image (v.afterSignedEntry root shelf header input count wires s d positive fit m))) :
    ∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor₀) j) (values j) v.resolver.lanes
      (v.beforeArgumentWrite root shelf header input count wires B s d positive fit m) :=by
  intro j loc
  have cap : v.resolver.rows≤v.resolver.rowCap:=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have inside:= (Nat.add_lt_add_left ((row _ _ _ loc).isLt.trans_le cap)
    (v.resolver.output (v.resolver.slot (v.normalizedEnd floor₀) j.val))).trans_le
    (v.resolver.within (v.normalizedEnd floor₀) j).2
  exact (v.post_vector_before_write root shelf header input count wires B s bank d positive fit m inside).trans
    (issued j loc)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
