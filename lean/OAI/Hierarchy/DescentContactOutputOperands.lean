import OAI.Hierarchy.DescentContactOutputShape
import OAI.Hierarchy.DescentContactLateMass
import OAI.Hierarchy.DescentContactDonorMarkers
import OAI.Hierarchy.DescentResetSignedHaloLate
import OAI.Hierarchy.DescentContactMarkerShape
import OAI.Hierarchy.DescentContactWidthPage
import OAI.Hierarchy.DescentContactCoordinateJoint
import OAI.Hierarchy.DescentResetDonorBook

namespace OAI
/-! # Four numerical outputs for each directed reset socket -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentContactSenderMass DescentContactDonorSelection
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (A : Shape) (donorStart first : ℕ)
set_option quotPrecheck false
local notation "D₀" => A.donor
local notation "N" => (D₀).lows*(2*(D₀).cap)
local notation "M" => (D₀).batch
local notation "b" => (D₀).fieldBits
local notation "t" => A.metaBits
local notation "C" => (D₀).markers donorStart A.shapes A.markerBits
local notation "rad" => 2^(Nat.clog 2 ((D₀).degree+2))
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
local notation "S₀" => (D₀).halo donorStart u.routes.roster

def socketWing (q : Fin A.sockets) : Bool×ℕ:=query (r:=(D₀).residual) (n:=(D₀).n) (Ht:=(D₀).height) q
def ownAt (q : Fin A.sockets) (j : Fin N) : Expr:=(C).priorView ((D₀).priorSensor donorStart (A.socketWing q).1 j 0)
def markAt (q : Fin A.sockets) (j : Fin N) : Expr:=
  .lookup ((C).output ((C).index q (finProdFinEquiv (finTwoEquiv.symm (A.socketWing q).1,j))).val) .row
def markFlag (q : Fin A.sockets) (j : Fin N) : Expr:=
  DescentStaticUnary.query (DescentContactMarkerShape.flag A.markerBits b) M (A.flagPage first) (A.markAt donorStart q j)
def otherAt (q : Fin A.sockets) (j : Fin N) : Expr:=
  DescentContactMarkerShape.port A.shapes A.markerBits t M (A.marker first) (A.markAt donorStart q j)
def ownShape : Expr:=DescentContactWidthPage.expr (A.countPage first) b t M (C).shapeView
def oldAt (end_ : Bool) (j : Fin N) : Expr:=
  let p:=finProdFinEquiv.symm j
  let chip:=Expr.lookup (u.signed p.1 p.2) .row
  let raw:=if end_ then DescentResetSignedHaloMatrix.Right.port (S₀) (DescentContactMaskShape.massEnd (D₀) first) chip else (S₀).port chip
  DescentContactWidthPage.expr (A.haloPage first) (D₀).cargoBits t M ((C).priorView raw)
def ownMass (q : Fin A.sockets) : Expr:=
  DescentContactWidthPage.expr (A.countPage first) b t M
    ((C).priorView (.lookup (DescentContactMaskShape.bank (D₀) donorStart first q) .row))
def endsAt (q : Fin A.sockets) (j : Fin N) (atEnd : Bool) : Expr:=
  DescentContactCoordinateJoint.expr rad (if atEnd=(A.socketWing q).1 then A.ownShape donorStart first else A.otherAt donorStart first q j)
    (A.oldAt donorStart first u atEnd j)
def witnessAt (q : Fin A.sockets) (j : Fin N) (side : Option Bool) : Expr:=
  let localEnd:=(A.socketWing q).1
  let pick:=DescentResetDonorBook.table (fun z=>(A.socketWing z).2) b t M (A.choicePage first) q.succ
  match side with
  | none=>A.endsAt donorStart first u q j localEnd
  | some e=>pick.read (ProtocolRAM.scale (A.socketWing q).2 (A.markFlag donorStart first q j)) (A.endsAt donorStart first u q j e)
def selectAt (q : Fin A.sockets) (end_ : Option Bool) : Expr:=
  DescentResetDonorBook.expression (fun i=>(A.socketWing i).2) b t M (A.choicePage first) q
    (A.ownAt donorStart q) (fun j=>A.witnessAt donorStart first u q j end_)
/-- Final layout is mass, original source, original target, and receiver. -/
def fieldsAt (q : Fin A.sockets) : Fin 4→Expr:=
  ![A.ownMass donorStart first q,A.selectAt donorStart first u q (some false),A.selectAt donorStart first u q (some true),
    A.selectAt donorStart first u q none]

theorem field_work (q : Fin A.sockets) (s : Option Bool) (cost : ℕ) (bounded : ∀j,
    (A.ownAt donorStart q j).work+(A.witnessAt donorStart first u q j s).work≤cost) :
    (A.selectAt donorStart first u q s).work≤1+N*(cost+22):=
  DescentResetDonorBook.price _ _ _ _ _ _ _ _ _ bounded

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
