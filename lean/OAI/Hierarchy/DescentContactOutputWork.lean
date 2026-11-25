import OAI.Hierarchy.DescentContactOutputIssued

namespace OAI
/-! # The emitted contact instruction count from the physical signed donor and socket dimensions -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentContactPreROM DescentContactProbePitch
open DescentResetSignedHaloMatrix DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
local notation "D" => A.donor
local notation "C₀" => (D).markers donorStart A.shapes A.markerBits
local notation "N" => (D).lows*(2*(D).cap)
local notation "rad" => 2^Nat.clog 2 ((D).degree+2)
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
local notation "chart" => (D).halo donorStart u.routes.roster

def haloWork := 12+8*(1+(A.donor.degree+1)*55)
def jointWork := 2+rad*20+A.haloWork
def operandWork := max 68 (1+N*(56+(12+20*A.sockets+A.jointWork)+22))

theorem lifted_work (x : Expr) : ((C₀).priorView x).work≤8*x.work:=by
  have before:=ProtocolRAM.Calendar.CatalogueRows.substitute_work x
    (DescentContactProbePitch.value (D).hosts A.shapes (D).groups (D).batch (D).fieldBits (C₀).pitchBase 0)
  change ((C₀).priorView x).work≤x.work*8 at before
  omega

private theorem unary_work {b v : ℕ} (law : Cell b→Cell 0→Cell v) (M root : ℕ) (x : Expr) :
    (DescentStaticUnary.query law M root x).work=x.work+12:=by
  rw [DescentStaticUnary.query,DescentPackedZip.work]
  change x.work+1+11=x.work+12
  omega

theorem oldAt_work (s : Bool) (j : Fin N) : (A.oldAt donorStart first u s j).work≤A.haloWork:=by
  let p : Fin (D).lows×Fin (2*(D).cap):=finProdFinEquiv.symm j
  let wire:=Expr.lookup (u.signed p.1 p.2) .row
  have one : ((chart).port wire).work=1+((D).degree+1)*55:=(chart).port_work wire
  have two : (Right.port (chart) (DescentContactMaskShape.massEnd (D) first) wire).work=1+((D).degree+1)*55:=by
    rw [Right.port,DescentPackedChildNeighbor.SIMD.work,List.length_finRange]
    simp only [Right.query,DescentPackedZip.work]
    rfl
  cases s <;> simp only [oldAt,Bool.false_eq_true,ite_false,ite_true,DescentContactWidthPage.expr,unary_work]
  · change ((C₀).priorView ((chart).port wire)).work+12≤12+8*(1+((D).degree+1)*55)
    have reduced:=A.lifted_work donorStart ((chart).port wire)
    rw [one] at reduced
    omega
  · change ((C₀).priorView (Right.port (chart) (DescentContactMaskShape.massEnd (D) first) wire)).work+12≤12+8*(1+((D).degree+1)*55)
    have reduced:=A.lifted_work donorStart (Right.port (chart) (DescentContactMaskShape.massEnd (D) first) wire)
    rw [two] at reduced
    omega

private theorem endpoint_work (q : Fin A.sockets) (j : Fin N) (side : Bool) :
    (A.endsAt donorStart first u q j side).work≤A.jointWork:=by
  have sh : (A.ownShape donorStart first).work=19:=by
    simp only [ownShape,DescentContactWidthPage.expr,DescentStaticUnary.query,DescentPackedZip.work]
    rfl
  have other : (A.otherAt donorStart first q j).work=19:=by
    simp only [otherAt,DescentContactMarkerShape.port,DescentStaticUnary.query,DescentPackedZip.work]
    rfl
  unfold endsAt
  rw [DescentContactCoordinateJoint.work]
  split <;> simp only [sh,other,Nat.reduceAdd]
  all_goals exact Nat.add_le_add_left (A.oldAt_work donorStart first u side j) _

theorem work_bound (q : Fin A.sockets) (f : Fin 4) :
    (A.fieldsAt donorStart first u q f).work≤A.operandWork:=by
  have cap : (A.socketWing q).2≤A.sockets:=by
    let j:=DescentResetLocalRoster.rootSlots (D).residual (2^(D).n)*(2^(D).n+2^(D).height)
    let p : Fin 2×Fin j:=finProdFinEquiv.symm q
    change p.2.val+1≤2*j
    have h:=p.2.isLt
    omega
  have own (j : Fin N): (A.ownAt donorStart q j).work≤56:=
    A.lifted_work donorStart ((D).priorSensor donorStart (A.socketWing q).1 j 0)
  have d (j : Fin N): (A.markFlag donorStart first q j).work=19:=by
    simp only [markFlag,DescentStaticUnary.query,DescentPackedZip.work]
    rfl
  have chosen (s : Option Bool) : (A.selectAt donorStart first u q s).work≤A.operandWork:=by
    apply le_trans (A.field_work donorStart first u q s (56+(12+20*A.sockets+A.jointWork)) _) (le_max_right ..)
    intro j
    apply Nat.add_le_add (own j)
    cases s with
    | none=>exact (A.endpoint_work donorStart first u q j (A.socketWing q).1).trans (Nat.le_add_left ..)
    | some side=>
      simp only [witnessAt,DescentPackedZip.work,ProtocolRAM.scale_work,d,Nat.reduceAdd]
      have e:=A.endpoint_work donorStart first u q j side
      omega
  have mass : (A.ownMass donorStart first q).work≤68:=by
    have h:=A.lifted_work donorStart (.lookup (DescentContactMaskShape.bank (D) donorStart first q) .row)
    simp only [ownMass,DescentContactWidthPage.expr,DescentStaticUnary.query,DescentPackedZip.work]
    change _ +1+11≤68
    change _≤8*7 at h
    omega
  fin_cases f
  · exact mass.trans (le_max_left ..)
  · exact chosen (some false)
  · exact chosen (some true)
  · exact chosen none

theorem priced (old : 0<(D).batch) (block : 0<A.blocks) (batch : 0<A.batch) :
    A.issuedTicks donorStart first u+7*names (A.issuedProgram donorStart first u w)≤
      A.cost donorStart first A.operandWork :=
  A.actual_cost donorStart first u A.operandWork (A.work_bound donorStart first u) old block batch

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
